#!/usr/bin/env python3
"""
F2FS Raw Image Reader
Browse and extract files from unsparsed F2FS .img files without mounting.
Designed for Termux on Android.

Usage:
    python fuck_f2fs.py <image.img> [command] [args]

Commands:
    info                    Show filesystem info
    ls [path]               List directory (default: /)
    tree [path] [depth]     Show directory tree
    cat <path>              Print file contents to stdout
    extract <path> [dest]   Extract file to dest (default: current dir)
    extractdir <path> [dest] Extract entire directory recursively
    find <pattern>          Search for files matching pattern
    debug [nid|path]        Debug NAT lookup for a node (default: root)
    cp                      Show checkpoint details
    hexdump <blkaddr> [n]   Hex dump of a raw block
"""

import struct
import sys
import os
import stat
import fnmatch
from datetime import datetime

# F2FS Constants
F2FS_MAGIC = 0xF2F52010
F2FS_BLKSIZE = 4096
F2FS_SB_OFFSET = 1024
F2FS_NAME_LEN = 255
F2FS_SLOT_LEN = 8
MAX_ACTIVE_LOGS = 16
MAX_ACTIVE_NODE_LOGS = 8
MAX_ACTIVE_DATA_LOGS = 8

# Inode inline flags
F2FS_INLINE_XATTR = 0x01
F2FS_INLINE_DATA = 0x02
F2FS_INLINE_DENTRY = 0x04
F2FS_DATA_EXIST = 0x08
F2FS_INLINE_DOTS = 0x10
F2FS_EXTRA_ATTR = 0x20

# File types in directory entries
FT_UNKNOWN = 0
FT_REG_FILE = 1
FT_DIR = 2
FT_CHRDEV = 3
FT_BLKDEV = 4
FT_FIFO = 5
FT_SOCK = 6
FT_SYMLINK = 7

FILE_TYPE_NAMES = {
    FT_UNKNOWN: '?', FT_REG_FILE: '-', FT_DIR: 'd',
    FT_CHRDEV: 'c', FT_BLKDEV: 'b', FT_FIFO: 'p',
    FT_SOCK: 's', FT_SYMLINK: 'l'
}

# Special addresses
NULL_ADDR = 0
NEW_ADDR = 0xFFFFFFFF
COMPRESS_ADDR = 0xFFFFFFFE

# Checkpoint flags
CP_LARGE_NAT_BITMAP_FLAG = 0x00000400

# NAT
NAT_ENTRY_SIZE = 9  # version(1) + ino(4) + block_addr(4)

# Directory entry
DIR_ENTRY_SIZE = 11  # hash(4) + ino(4) + name_len(2) + file_type(1)
NR_DENTRY_IN_BLOCK = 214
DENTRY_BITMAP_SIZE = 27  # ceil(214/8)

# Node footer
NODE_FOOTER_SIZE = 24


class F2FSReader:
    def __init__(self, image_path):
        self.image_path = image_path
        self.f = open(image_path, 'rb')
        self.sb = {}
        self.block_size = F2FS_BLKSIZE
        self.blocks_per_seg = 0
        self.nat_bitmap = None
        self.nat_entries_per_block = 0
        self._parse_superblock()
        self._parse_checkpoint()

    def close(self):
        self.f.close()

    def _read_block(self, blkaddr):
        """Read a single block from the image."""
        self.f.seek(blkaddr * self.block_size)
        return self.f.read(self.block_size)

    def _read_bytes(self, offset, size):
        """Read arbitrary bytes from the image."""
        self.f.seek(offset)
        return self.f.read(size)

    def _parse_superblock(self):
        """Parse the F2FS superblock at offset 1024."""
        data = self._read_bytes(F2FS_SB_OFFSET, 512)
        sb = self.sb

        magic = struct.unpack_from('<I', data, 0)[0]
        if magic != F2FS_MAGIC:
            raise ValueError(f"Not an F2FS image (magic: 0x{magic:08X}, expected 0x{F2FS_MAGIC:08X})")

        sb['magic'] = magic
        sb['major_ver'] = struct.unpack_from('<H', data, 4)[0]
        sb['minor_ver'] = struct.unpack_from('<H', data, 6)[0]
        sb['log_sectorsize'] = struct.unpack_from('<I', data, 8)[0]
        sb['log_sectors_per_block'] = struct.unpack_from('<I', data, 12)[0]
        sb['log_blocksize'] = struct.unpack_from('<I', data, 16)[0]
        sb['log_blocks_per_seg'] = struct.unpack_from('<I', data, 20)[0]
        sb['segs_per_sec'] = struct.unpack_from('<I', data, 24)[0]
        sb['secs_per_zone'] = struct.unpack_from('<I', data, 28)[0]
        sb['checksum_offset'] = struct.unpack_from('<I', data, 32)[0]
        sb['block_count'] = struct.unpack_from('<Q', data, 36)[0]
        sb['section_count'] = struct.unpack_from('<I', data, 44)[0]
        sb['segment_count'] = struct.unpack_from('<I', data, 48)[0]
        sb['segment_count_ckpt'] = struct.unpack_from('<I', data, 52)[0]
        sb['segment_count_sit'] = struct.unpack_from('<I', data, 56)[0]
        sb['segment_count_nat'] = struct.unpack_from('<I', data, 60)[0]
        sb['segment_count_ssa'] = struct.unpack_from('<I', data, 64)[0]
        sb['segment_count_main'] = struct.unpack_from('<I', data, 68)[0]
        sb['segment0_blkaddr'] = struct.unpack_from('<I', data, 72)[0]
        sb['cp_blkaddr'] = struct.unpack_from('<I', data, 76)[0]
        sb['sit_blkaddr'] = struct.unpack_from('<I', data, 80)[0]
        sb['nat_blkaddr'] = struct.unpack_from('<I', data, 84)[0]
        sb['ssa_blkaddr'] = struct.unpack_from('<I', data, 88)[0]
        sb['main_blkaddr'] = struct.unpack_from('<I', data, 92)[0]
        sb['root_ino'] = struct.unpack_from('<I', data, 96)[0]
        sb['node_ino'] = struct.unpack_from('<I', data, 100)[0]
        sb['meta_ino'] = struct.unpack_from('<I', data, 104)[0]

        # Parse volume name (UTF-16LE, 512 bytes max at offset 0x1AC in superblock)
        try:
            vol_name_data = self._read_bytes(F2FS_SB_OFFSET + 0x6C, 512)
            sb['volume_name'] = vol_name_data.decode('utf-16-le').rstrip('\x00')
        except:
            sb['volume_name'] = ''

        self.block_size = 1 << sb['log_blocksize']
        self.blocks_per_seg = 1 << sb['log_blocks_per_seg']
        self.nat_entries_per_block = self.block_size // NAT_ENTRY_SIZE

    def _parse_checkpoint(self):
        """Parse checkpoint to extract NAT version bitmap.
        
        Checkpoint structure layout (all offsets in bytes):
          0: checkpoint_ver (u64)
          8: user_block_count (u64)
         16: valid_block_count (u64)
         24: rsvd_segment_count (u32)
         28: overprov_segment_count (u32)
         32: free_segment_count (u32)
         36: cur_node_segno[8] (u32 * 8 = 32 bytes)
         68: cur_node_blkoff[8] (u16 * 8 = 16 bytes)  ← these are __le16!
         84: cur_data_segno[8] (u32 * 8 = 32 bytes)
        116: cur_data_blkoff[8] (u16 * 8 = 16 bytes)  ← these are __le16!
        132: ckpt_flags (u32)
        136: cp_pack_total_block_count (u32)
        140: cp_pack_start_sum (u32)
        144: valid_node_count (u32)
        148: valid_inode_count (u32)
        152: next_free_nid (u32)
        156: sit_ver_bitmap_bytesize (u32)
        160: nat_ver_bitmap_bytesize (u32)
        164: checksum_offset (u32)
        168: elapsed_time (u64)
        176: alloc_type[MAX_ACTIVE_LOGS=16] (u8 * 16)
        192: sit_nat_version_bitmap[]
        """
        cp_blkaddr = self.sb['cp_blkaddr']
        cp_data = self._read_block(cp_blkaddr)

        cp = {}
        cp['checkpoint_ver'] = struct.unpack_from('<Q', cp_data, 0)[0]
        cp['user_block_count'] = struct.unpack_from('<Q', cp_data, 8)[0]
        cp['valid_block_count'] = struct.unpack_from('<Q', cp_data, 16)[0]
        cp['rsvd_segment_count'] = struct.unpack_from('<I', cp_data, 24)[0]
        cp['overprov_segment_count'] = struct.unpack_from('<I', cp_data, 28)[0]
        cp['free_segment_count'] = struct.unpack_from('<I', cp_data, 32)[0]

        # Fixed offset for ckpt_flags after the segno/blkoff arrays
        cp['ckpt_flags'] = struct.unpack_from('<I', cp_data, 132)[0]
        cp['cp_pack_total_block_count'] = struct.unpack_from('<I', cp_data, 136)[0]
        cp['cp_pack_start_sum'] = struct.unpack_from('<I', cp_data, 140)[0]
        cp['valid_node_count'] = struct.unpack_from('<I', cp_data, 144)[0]
        cp['valid_inode_count'] = struct.unpack_from('<I', cp_data, 148)[0]
        cp['next_free_nid'] = struct.unpack_from('<I', cp_data, 152)[0]
        cp['sit_ver_bitmap_bytesize'] = struct.unpack_from('<I', cp_data, 156)[0]
        cp['nat_ver_bitmap_bytesize'] = struct.unpack_from('<I', cp_data, 160)[0]
        cp['checksum_offset'] = struct.unpack_from('<I', cp_data, 164)[0]

        self.cp = cp

        sit_bm_size = cp['sit_ver_bitmap_bytesize']
        nat_bm_size = cp['nat_ver_bitmap_bytesize']

        # Bitmap starts at fixed offset 192 in the checkpoint block
        # (after elapsed_time at 168 and alloc_type[16] at 176)
        BM_OFFSET = 192

        # Check for CP_LARGE_NAT_BITMAP_FLAG - if set, bitmap is in a separate block
        if cp['ckpt_flags'] & CP_LARGE_NAT_BITMAP_FLAG:
            # Large bitmap: stored in the block after checkpoint
            try:
                bm_block = self._read_block(cp_blkaddr + 1)
                # NAT bitmap comes first in large bitmap mode
                self.nat_bitmap = bm_block[:nat_bm_size]
            except:
                self.nat_bitmap = None
        elif BM_OFFSET + sit_bm_size + nat_bm_size <= self.block_size:
            # Normal: SIT bitmap first, then NAT bitmap, both in checkpoint block
            nat_start = BM_OFFSET + sit_bm_size
            self.nat_bitmap = cp_data[nat_start:nat_start + nat_bm_size]
        else:
            # Bitmap overflows checkpoint block - read from next block
            try:
                overflow = BM_OFFSET + sit_bm_size + nat_bm_size - self.block_size
                if overflow > 0 and BM_OFFSET + sit_bm_size < self.block_size:
                    # NAT bitmap split across two blocks
                    part1_len = self.block_size - (BM_OFFSET + sit_bm_size)
                    part1 = cp_data[BM_OFFSET + sit_bm_size:]
                    bm_block = self._read_block(cp_blkaddr + 1)
                    part2 = bm_block[:nat_bm_size - part1_len]
                    self.nat_bitmap = part1 + part2
                else:
                    bm_block = self._read_block(cp_blkaddr + 1)
                    nat_offset = sit_bm_size - (self.block_size - BM_OFFSET)
                    if nat_offset < 0:
                        nat_offset = 0
                    self.nat_bitmap = bm_block[nat_offset:nat_offset + nat_bm_size]
            except:
                self.nat_bitmap = None

    def _nat_block_is_set1(self, block_idx):
        """Check if a NAT block uses set 1 (vs set 0) based on version bitmap."""
        if self.nat_bitmap is None:
            return False
        byte_idx = block_idx // 8
        bit_idx = block_idx % 8
        if byte_idx >= len(self.nat_bitmap):
            return False
        return bool(self.nat_bitmap[byte_idx] & (1 << bit_idx))

    def _get_nat_entry(self, nid):
        """Look up a NAT entry for the given node ID. Returns (ino, block_addr)."""
        entries_per_block = self.nat_entries_per_block
        block_off = nid // entries_per_block
        entry_off = nid % entries_per_block

        nat_blkaddr = self.sb['nat_blkaddr']
        max_blkaddr = self.sb['block_count']

        # Calculate physical block for both NAT sets
        seg_off = block_off // self.blocks_per_seg
        blk_in_seg = block_off % self.blocks_per_seg

        set0_blk = nat_blkaddr + seg_off * 2 * self.blocks_per_seg + blk_in_seg
        set1_blk = nat_blkaddr + (seg_off * 2 + 1) * self.blocks_per_seg + blk_in_seg

        def read_entry(phys_blk):
            data = self._read_block(phys_blk)
            off = entry_off * NAT_ENTRY_SIZE
            version = data[off]
            ino = struct.unpack_from('<I', data, off + 1)[0]
            block_addr = struct.unpack_from('<I', data, off + 5)[0]
            return ino, block_addr

        # Try bitmap-indicated set first
        if self._nat_block_is_set1(block_off):
            primary, secondary = set1_blk, set0_blk
        else:
            primary, secondary = set0_blk, set1_blk

        ino, block_addr = read_entry(primary)

        # Validate: block_addr should be within filesystem bounds
        if block_addr != 0 and block_addr != NEW_ADDR and block_addr < max_blkaddr:
            return ino, block_addr

        # Fallback: try other set
        ino2, block_addr2 = read_entry(secondary)
        if block_addr2 != 0 and block_addr2 != NEW_ADDR and block_addr2 < max_blkaddr:
            return ino2, block_addr2

        # Return whatever we got from primary
        return ino, block_addr

    def _read_node(self, nid):
        """Read a node block by its node ID. Returns raw block data."""
        ino, blkaddr = self._get_nat_entry(nid)
        if blkaddr == 0 or blkaddr == NEW_ADDR:
            return None
        data = self._read_block(blkaddr)
        # Validate node footer: footer_nid should match requested nid
        footer_nid = struct.unpack_from('<I', data, 4072)[0]
        footer_ino = struct.unpack_from('<I', data, 4076)[0]
        if footer_nid != nid:
            # Node validation failed - might be reading wrong block
            # Try the other NAT set explicitly
            entries_per_block = self.nat_entries_per_block
            block_off = nid // entries_per_block
            entry_off = nid % entries_per_block
            nat_blkaddr = self.sb['nat_blkaddr']
            seg_off = block_off // self.blocks_per_seg
            blk_in_seg = block_off % self.blocks_per_seg

            for s in [0, 1]:
                alt_blk = nat_blkaddr + (seg_off * 2 + s) * self.blocks_per_seg + blk_in_seg
                if alt_blk == blkaddr:
                    continue
                alt_data = self._read_block(alt_blk)
                off = entry_off * NAT_ENTRY_SIZE
                alt_addr = struct.unpack_from('<I', alt_data, off + 5)[0]
                if alt_addr == 0 or alt_addr == NEW_ADDR or alt_addr >= self.sb['block_count']:
                    continue
                alt_node = self._read_block(alt_addr)
                alt_footer_nid = struct.unpack_from('<I', alt_node, 4072)[0]
                if alt_footer_nid == nid:
                    return alt_node
        return data

    def debug_nid(self, nid):
        """Print debug info for a specific node ID."""
        print(f"Debug info for NID {nid}")
        print(f"{'=' * 50}")

        entries_per_block = self.nat_entries_per_block
        block_off = nid // entries_per_block
        entry_off = nid % entries_per_block
        nat_blkaddr = self.sb['nat_blkaddr']
        seg_off = block_off // self.blocks_per_seg
        blk_in_seg = block_off % self.blocks_per_seg

        set0_blk = nat_blkaddr + seg_off * 2 * self.blocks_per_seg + blk_in_seg
        set1_blk = nat_blkaddr + (seg_off * 2 + 1) * self.blocks_per_seg + blk_in_seg
        bitmap_says = "set1" if self._nat_block_is_set1(block_off) else "set0"

        print(f"  NAT block offset: {block_off}, entry offset: {entry_off}")
        print(f"  NAT set0 block: {set0_blk}, set1 block: {set1_blk}")
        print(f"  Bitmap indicates: {bitmap_says}")

        for label, phys_blk in [("set0", set0_blk), ("set1", set1_blk)]:
            data = self._read_block(phys_blk)
            off = entry_off * NAT_ENTRY_SIZE
            version = data[off]
            ino = struct.unpack_from('<I', data, off + 1)[0]
            block_addr = struct.unpack_from('<I', data, off + 5)[0]
            print(f"  {label}: version={version}, ino={ino}, blkaddr={block_addr}", end='')
            if block_addr != 0 and block_addr != NEW_ADDR and block_addr < self.sb['block_count']:
                node_data = self._read_block(block_addr)
                footer_nid = struct.unpack_from('<I', node_data, 4072)[0]
                footer_ino = struct.unpack_from('<I', node_data, 4076)[0]
                match = "✓" if footer_nid == nid else "✗"
                print(f" → footer_nid={footer_nid} {match}, footer_ino={footer_ino}")
            else:
                print(f" (invalid/null)")

        # Show resolved result
        node_data = self._read_node(nid)
        if node_data:
            inode = self._parse_inode(node_data)
            print(f"\n  Resolved inode:")
            print(f"    mode: 0o{inode['i_mode']:o}")
            print(f"    size: {inode['i_size']}")
            print(f"    name: {inode['i_name']}")
            print(f"    inline flags: 0x{inode['i_inline']:02x}", end='')
            flags = []
            if inode['i_inline'] & F2FS_INLINE_XATTR: flags.append('INLINE_XATTR')
            if inode['i_inline'] & F2FS_INLINE_DATA: flags.append('INLINE_DATA')
            if inode['i_inline'] & F2FS_INLINE_DENTRY: flags.append('INLINE_DENTRY')
            if inode['i_inline'] & F2FS_EXTRA_ATTR: flags.append('EXTRA_ATTR')
            if inode['i_inline'] & F2FS_DATA_EXIST: flags.append('DATA_EXIST')
            if flags: print(f" ({', '.join(flags)})")
            else: print()
            print(f"    addr_start: {inode['_addr_start']}")
            print(f"    total_addr_slots: {inode['_total_addr_slots']}")
            print(f"    inline_xattr_size: {inode['_inline_xattr_size']}")
            print(f"    data addrs (after xattr): {inode['_num_addrs']}")
            # Show first few non-zero addresses
            nonzero = [(i, a) for i, a in enumerate(inode['i_addr'][:20])
                       if a != 0 and a != NEW_ADDR]
            if nonzero:
                print(f"    first data blocks: {nonzero[:5]}")
            print(f"    i_nid[5]: {inode['i_nid']}")
        else:
            print(f"\n  Could not read node!")

    def _parse_inode(self, data):
        """Parse an inode from a node block. Returns dict of inode fields."""
        if data is None:
            return None

        inode = {}
        inode['i_mode'] = struct.unpack_from('<H', data, 0)[0]
        inode['i_advise'] = data[2]
        inode['i_inline'] = data[3]
        inode['i_uid'] = struct.unpack_from('<I', data, 4)[0]
        inode['i_gid'] = struct.unpack_from('<I', data, 8)[0]
        inode['i_links'] = struct.unpack_from('<I', data, 12)[0]
        inode['i_size'] = struct.unpack_from('<Q', data, 16)[0]
        inode['i_blocks'] = struct.unpack_from('<Q', data, 24)[0]
        inode['i_atime'] = struct.unpack_from('<Q', data, 32)[0]
        inode['i_ctime'] = struct.unpack_from('<Q', data, 40)[0]
        inode['i_mtime'] = struct.unpack_from('<Q', data, 48)[0]
        inode['i_current_depth'] = struct.unpack_from('<I', data, 72)[0]
        inode['i_xattr_nid'] = struct.unpack_from('<I', data, 76)[0]
        inode['i_flags'] = struct.unpack_from('<I', data, 80)[0]
        inode['i_pino'] = struct.unpack_from('<I', data, 84)[0]
        inode['i_namelen'] = struct.unpack_from('<I', data, 88)[0]

        name_len = min(inode['i_namelen'], F2FS_NAME_LEN)
        try:
            inode['i_name'] = data[92:92 + name_len].decode('utf-8', errors='replace')
        except:
            inode['i_name'] = ''

        # i_ext at offset 348 (12 bytes)
        # i_addr starts at offset 360 (or 360 + extra_isize if EXTRA_ATTR)
        inode['_raw'] = data  # keep raw data for address extraction

        addr_start = 360
        extra_isize = 0
        inline_xattr_size = 0

        if inode['i_inline'] & F2FS_EXTRA_ATTR:
            extra_isize = struct.unpack_from('<H', data, 360)[0]
            # i_inline_xattr_size is at offset 362 (right after i_extra_isize)
            inline_xattr_size = struct.unpack_from('<H', data, 362)[0]
            addr_start = 360 + extra_isize

        inode['_addr_start'] = addr_start
        inode['_extra_isize'] = extra_isize
        inode['_inline_xattr_size'] = inline_xattr_size

        # Calculate total address slots in the inode
        # i_nid[5] starts at 4072 - 20 = 4052
        total_addr_slots = (4052 - addr_start) // 4

        # If INLINE_XATTR is set, the last inline_xattr_size slots are
        # reserved for xattr data, NOT data block addresses
        if inode['i_inline'] & F2FS_INLINE_XATTR:
            if inline_xattr_size > 0:
                xattr_slots = inline_xattr_size
            else:
                # Default: 50 slots (200 bytes) when no explicit size
                xattr_slots = 50
            num_data_addrs = total_addr_slots - xattr_slots
        else:
            num_data_addrs = total_addr_slots

        inode['_num_addrs'] = num_data_addrs
        inode['_total_addr_slots'] = total_addr_slots

        # Read ONLY the data addresses (not the xattr area)
        inode['i_addr'] = []
        for i in range(num_data_addrs):
            addr = struct.unpack_from('<I', data, addr_start + i * 4)[0]
            inode['i_addr'].append(addr)

        # Read i_nid[5] (just before footer)
        nid_start = 4072 - 20
        inode['i_nid'] = []
        for i in range(5):
            nid = struct.unpack_from('<I', data, nid_start + i * 4)[0]
            inode['i_nid'].append(nid)

        # Node footer
        inode['_footer_nid'] = struct.unpack_from('<I', data, 4072)[0]
        inode['_footer_ino'] = struct.unpack_from('<I', data, 4076)[0]

        return inode

    def get_inode(self, nid):
        """Get parsed inode for a node ID."""
        data = self._read_node(nid)
        if data is None:
            return None
        return self._parse_inode(data)

    def _read_dentry_block(self, data):
        """Parse a directory entry block. Returns list of (name, ino, file_type)."""
        entries = []

        # Bitmap at start
        bitmap = data[:DENTRY_BITMAP_SIZE]
        # Reserved bytes after bitmap
        reserved = data[DENTRY_BITMAP_SIZE:DENTRY_BITMAP_SIZE + 3]

        # Directory entries start at offset 30 (27 bitmap + 3 reserved)
        dentry_start = DENTRY_BITMAP_SIZE + 3  # 30

        # Filename area starts after all dentries
        fname_start = dentry_start + NR_DENTRY_IN_BLOCK * DIR_ENTRY_SIZE
        # = 30 + 214*11 = 30 + 2354 = 2384

        i = 0
        while i < NR_DENTRY_IN_BLOCK:
            byte_idx = i // 8
            bit_idx = i % 8

            if byte_idx >= len(bitmap) or not (bitmap[byte_idx] & (1 << bit_idx)):
                i += 1
                continue

            off = dentry_start + i * DIR_ENTRY_SIZE
            if off + DIR_ENTRY_SIZE > len(data):
                break

            hash_code = struct.unpack_from('<I', data, off)[0]
            ino = struct.unpack_from('<I', data, off + 4)[0]
            name_len = struct.unpack_from('<H', data, off + 8)[0]
            file_type = data[off + 10]

            # Read filename from slots
            slots_needed = (name_len + F2FS_SLOT_LEN - 1) // F2FS_SLOT_LEN
            fname_off = fname_start + i * F2FS_SLOT_LEN
            if fname_off + name_len <= len(data):
                try:
                    name = data[fname_off:fname_off + name_len].decode('utf-8', errors='replace')
                except:
                    name = f'<ino:{ino}>'
            else:
                name = f'<ino:{ino}>'

            if ino > 0 and name_len > 0:
                entries.append((name, ino, file_type))

            # Skip slots used by this entry
            i += max(slots_needed, 1)

        return entries

    def _read_inline_dentry(self, inode):
        """Parse inline directory entries from inode's i_addr area."""
        data = inode['_raw']
        addr_start = inode['_addr_start']

        # Available space = data address slots only (excludes xattr area)
        available = inode['_num_addrs'] * 4

        inline_data = data[addr_start:addr_start + available]

        # Calculate inline dentry layout
        # Layout: bitmap | reserved | dentries | filenames
        # nr_dentry is calculated so everything fits
        # bits_per_slot = 1 bit in bitmap, 11 bytes dentry, 8 bytes fname = 19 bytes + 1/8 bit
        # nr_dentry = floor(available * 8 / (8 * 19 + 1)) approximately
        # But F2FS uses a specific formula; let me use a practical approach

        # Try to detect: the bitmap is at the start, then dentries, then filenames
        # We need to figure out NR_INLINE_DENTRY
        # Formula: nr = (available - bitmap_size - reserved) / (11 + 8)
        # where bitmap_size = ceil(nr / 8)
        # Solving: nr * 19 + ceil(nr/8) + reserved <= available

        # Iterative solve
        nr = 0
        for test_nr in range(1, 1000):
            bm = (test_nr + 7) // 8
            total = bm + 4 + test_nr * DIR_ENTRY_SIZE + test_nr * F2FS_SLOT_LEN  # 4 bytes reserved for inline
            if total > available:
                nr = test_nr - 1
                break
        else:
            nr = test_nr

        if nr <= 0:
            return []

        bm_size = (nr + 7) // 8
        # Some F2FS versions use different reserved sizes; try common layout
        # Layout: bitmap[bm_size] + reserved[?] + dentries[nr*11] + filenames[nr*8]
        # The reserved fills the gap

        dentry_area_size = nr * DIR_ENTRY_SIZE
        fname_area_size = nr * F2FS_SLOT_LEN
        reserved_size = available - bm_size - dentry_area_size - fname_area_size

        if reserved_size < 0:
            # Adjust nr down
            nr -= 1
            bm_size = (nr + 7) // 8
            dentry_area_size = nr * DIR_ENTRY_SIZE
            fname_area_size = nr * F2FS_SLOT_LEN
            reserved_size = available - bm_size - dentry_area_size - fname_area_size

        bitmap = inline_data[:bm_size]
        dentry_start = bm_size + reserved_size
        fname_start = dentry_start + dentry_area_size

        entries = []
        i = 0
        while i < nr:
            byte_idx = i // 8
            bit_idx = i % 8

            if byte_idx >= len(bitmap) or not (bitmap[byte_idx] & (1 << bit_idx)):
                i += 1
                continue

            off = dentry_start + i * DIR_ENTRY_SIZE
            if off + DIR_ENTRY_SIZE > len(inline_data):
                break

            hash_code = struct.unpack_from('<I', inline_data, off)[0]
            ino = struct.unpack_from('<I', inline_data, off + 4)[0]
            name_len = struct.unpack_from('<H', inline_data, off + 8)[0]
            file_type = inline_data[off + 10]

            slots_needed = (name_len + F2FS_SLOT_LEN - 1) // F2FS_SLOT_LEN
            fname_off = fname_start + i * F2FS_SLOT_LEN
            if fname_off + name_len <= len(inline_data):
                try:
                    name = inline_data[fname_off:fname_off + name_len].decode('utf-8', errors='replace')
                except:
                    name = f'<ino:{ino}>'
            else:
                name = f'<ino:{ino}>'

            if ino > 0 and name_len > 0:
                entries.append((name, ino, file_type))

            i += max(slots_needed, 1)

        return entries

    def _get_data_blocks(self, inode):
        """Get list of data block addresses for an inode, handling indirect blocks."""
        blocks = []

        # Direct addresses from inode
        for addr in inode['i_addr']:
            if addr == NULL_ADDR or addr == NEW_ADDR or addr == COMPRESS_ADDR:
                blocks.append(None)
            else:
                blocks.append(addr)

        # Single indirect nodes: i_nid[0] and i_nid[1]
        for idx in range(2):
            nid = inode['i_nid'][idx]
            if nid == 0:
                continue
            node_data = self._read_node(nid)
            if node_data is None:
                continue
            # Direct node: 1018 addresses
            for i in range(1018):
                addr = struct.unpack_from('<I', node_data, i * 4)[0]
                if addr == NULL_ADDR or addr == NEW_ADDR or addr == COMPRESS_ADDR:
                    blocks.append(None)
                else:
                    blocks.append(addr)

        # Double indirect nodes: i_nid[2] and i_nid[3]
        for idx in range(2, 4):
            nid = inode['i_nid'][idx]
            if nid == 0:
                continue
            node_data = self._read_node(nid)
            if node_data is None:
                continue
            # Indirect node: 1018 nids pointing to direct nodes
            for i in range(1018):
                child_nid = struct.unpack_from('<I', node_data, i * 4)[0]
                if child_nid == 0:
                    continue
                child_data = self._read_node(child_nid)
                if child_data is None:
                    continue
                for j in range(1018):
                    addr = struct.unpack_from('<I', child_data, j * 4)[0]
                    if addr == NULL_ADDR or addr == NEW_ADDR or addr == COMPRESS_ADDR:
                        blocks.append(None)
                    else:
                        blocks.append(addr)

        # Triple indirect: i_nid[4] - rarely used, skip for now

        return blocks

    def list_dir(self, nid):
        """List directory entries for a given directory inode NID."""
        inode = self.get_inode(nid)
        if inode is None:
            return []

        # Check if inline dentry
        if inode['i_inline'] & F2FS_INLINE_DENTRY:
            return self._read_inline_dentry(inode)

        # Regular directory - read data blocks
        entries = []
        blocks = self._get_data_blocks(inode)
        file_size = inode['i_size']
        blocks_needed = (file_size + self.block_size - 1) // self.block_size

        for i, blkaddr in enumerate(blocks):
            if i >= blocks_needed:
                break
            if blkaddr is None:
                continue
            data = self._read_block(blkaddr)
            entries.extend(self._read_dentry_block(data))

        return entries

    def read_file(self, nid, max_size=None):
        """Read file contents by inode NID. Returns bytes."""
        inode = self.get_inode(nid)
        if inode is None:
            return b''

        file_size = inode['i_size']
        if max_size is not None:
            file_size = min(file_size, max_size)

        # Check for inline data
        if inode['i_inline'] & F2FS_INLINE_DATA:
            data = inode['_raw']
            addr_start = inode['_addr_start']
            available = inode['_num_addrs'] * 4
            return data[addr_start:addr_start + min(file_size, available)]

        # Regular file - read data blocks
        result = bytearray()
        blocks = self._get_data_blocks(inode)
        remaining = file_size

        for blkaddr in blocks:
            if remaining <= 0:
                break
            if blkaddr is None:
                # Hole - zero fill
                chunk = min(remaining, self.block_size)
                result.extend(b'\x00' * chunk)
            else:
                data = self._read_block(blkaddr)
                chunk = min(remaining, self.block_size)
                result.extend(data[:chunk])
            remaining -= chunk

        return bytes(result)

    def resolve_path(self, path):
        """Resolve a filesystem path to an inode NID. Returns (nid, inode) or (None, None)."""
        if path in ('/', ''):
            nid = self.sb['root_ino']
            return nid, self.get_inode(nid)

        path = path.strip('/')
        parts = path.split('/')

        current_nid = self.sb['root_ino']

        for part in parts:
            if not part:
                continue
            entries = self.list_dir(current_nid)
            found = False
            for name, ino, ft in entries:
                if name == part:
                    current_nid = ino
                    found = True
                    break
            if not found:
                return None, None

        return current_nid, self.get_inode(current_nid)

    def print_info(self):
        """Print filesystem information."""
        sb = self.sb
        print(f"F2FS Filesystem Info")
        print(f"{'=' * 50}")
        print(f"  Version:          {sb['major_ver']}.{sb['minor_ver']}")
        print(f"  Volume:           {sb.get('volume_name', 'N/A')}")
        print(f"  Block size:       {self.block_size}")
        print(f"  Blocks/segment:   {self.blocks_per_seg}")
        print(f"  Total blocks:     {sb['block_count']}")
        total_mb = sb['block_count'] * self.block_size / (1024 * 1024)
        print(f"  Total size:       {total_mb:.1f} MB")
        print(f"  Segments:         {sb['segment_count']}")
        print(f"  Main segments:    {sb['segment_count_main']}")
        print(f"  Root inode:       {sb['root_ino']}")
        print(f"  NAT segments:     {sb['segment_count_nat']}")
        print(f"  SIT segments:     {sb['segment_count_sit']}")
        print(f"  CP blkaddr:       {sb['cp_blkaddr']}")
        print(f"  NAT blkaddr:      {sb['nat_blkaddr']}")
        print(f"  Main blkaddr:     {sb['main_blkaddr']}")
        if hasattr(self, 'cp'):
            cp = self.cp
            print(f"  Valid blocks:     {cp.get('valid_block_count', 'N/A')}")
            print(f"  Valid inodes:     {cp.get('valid_inode_count', 'N/A')}")
            print(f"  Valid nodes:      {cp.get('valid_node_count', 'N/A')}")

    def format_mode(self, mode):
        """Format file mode to ls-style string."""
        result = ''
        if stat.S_ISDIR(mode):
            result += 'd'
        elif stat.S_ISLNK(mode):
            result += 'l'
        elif stat.S_ISCHR(mode):
            result += 'c'
        elif stat.S_ISBLK(mode):
            result += 'b'
        elif stat.S_ISFIFO(mode):
            result += 'p'
        elif stat.S_ISSOCK(mode):
            result += 's'
        else:
            result += '-'

        for who in ('USR', 'GRP', 'OTH'):
            for perm, char in [('R', 'r'), ('W', 'w'), ('X', 'x')]:
                flag = getattr(stat, f'S_I{perm}{who}')
                result += char if mode & flag else '-'

        return result

    def print_ls(self, path='/'):
        """Print directory listing."""
        nid, inode = self.resolve_path(path)
        if inode is None:
            print(f"Error: path '{path}' not found")
            return

        if not stat.S_ISDIR(inode['i_mode']):
            # It's a file, show info about it
            size = inode['i_size']
            mtime = datetime.fromtimestamp(inode['i_mtime']).strftime('%Y-%m-%d %H:%M')
            mode_str = self.format_mode(inode['i_mode'])
            name = path.split('/')[-1]
            print(f"{mode_str} {inode['i_uid']:5d} {inode['i_gid']:5d} {size:>10d} {mtime} {name}")
            return

        entries = self.list_dir(nid)
        if not entries:
            print(f"(empty directory)")
            return

        # Sort: directories first, then by name
        entries.sort(key=lambda e: (0 if e[2] == FT_DIR else 1, e[0]))

        for name, ino, ft in entries:
            child_inode = self.get_inode(ino)
            if child_inode is None:
                type_char = FILE_TYPE_NAMES.get(ft, '?')
                print(f"{type_char}?????????     ?     ?          ? ???????????? {name}")
                continue

            size = child_inode['i_size']
            mtime = datetime.fromtimestamp(child_inode['i_mtime']).strftime('%Y-%m-%d %H:%M')
            mode_str = self.format_mode(child_inode['i_mode'])
            uid = child_inode['i_uid']
            gid = child_inode['i_gid']

            suffix = ''
            if ft == FT_DIR:
                suffix = '/'
            elif ft == FT_SYMLINK:
                # Read symlink target
                try:
                    target = self.read_file(ino, max_size=4096).decode('utf-8', errors='replace')
                    suffix = f' -> {target}'
                except:
                    suffix = ' -> ?'

            print(f"{mode_str} {uid:5d} {gid:5d} {size:>10d} {mtime} {name}{suffix}")

    def print_tree(self, path='/', depth=3, prefix='', current_depth=0):
        """Print directory tree."""
        if current_depth >= depth:
            return

        nid, inode = self.resolve_path(path)
        if inode is None:
            return

        if current_depth == 0:
            print(path)

        entries = self.list_dir(nid)
        entries.sort(key=lambda e: (0 if e[2] == FT_DIR else 1, e[0]))

        # Filter out . and ..
        entries = [(n, i, t) for n, i, t in entries if n not in ('.', '..')]

        for idx, (name, ino, ft) in enumerate(entries):
            is_last = idx == len(entries) - 1
            connector = '└── ' if is_last else '├── '
            suffix = '/' if ft == FT_DIR else ''
            print(f"{prefix}{connector}{name}{suffix}")

            if ft == FT_DIR:
                extension = '    ' if is_last else '│   '
                child_path = f"{path.rstrip('/')}/{name}"
                self.print_tree(child_path, depth, prefix + extension, current_depth + 1)

    def cat_file(self, path):
        """Print file contents to stdout."""
        nid, inode = self.resolve_path(path)
        if inode is None:
            print(f"Error: '{path}' not found", file=sys.stderr)
            return

        if stat.S_ISDIR(inode['i_mode']):
            print(f"Error: '{path}' is a directory", file=sys.stderr)
            return

        if stat.S_ISLNK(inode['i_mode']):
            target = self.read_file(nid, max_size=4096).decode('utf-8', errors='replace')
            print(f"(symlink -> {target})")
            return

        data = self.read_file(nid)

        # Try text output first
        try:
            text = data.decode('utf-8')
            sys.stdout.write(text)
            if not text.endswith('\n'):
                print()
        except UnicodeDecodeError:
            # Binary file
            print(f"(binary file, {len(data)} bytes)", file=sys.stderr)
            sys.stdout.buffer.write(data)

    def extract_file(self, path, dest=None):
        """Extract a file from the image."""
        nid, inode = self.resolve_path(path)
        if inode is None:
            print(f"Error: '{path}' not found", file=sys.stderr)
            return False

        if stat.S_ISDIR(inode['i_mode']):
            print(f"Error: '{path}' is a directory (use extractdir)", file=sys.stderr)
            return False

        filename = path.split('/')[-1]
        if dest is None:
            dest = filename
        elif os.path.isdir(dest):
            dest = os.path.join(dest, filename)

        data = self.read_file(nid)
        with open(dest, 'wb') as out:
            out.write(data)

        print(f"Extracted: {path} -> {dest} ({len(data)} bytes)")
        return True

    def extract_dir(self, path, dest=None):
        """Extract a directory recursively."""
        nid, inode = self.resolve_path(path)
        if inode is None:
            print(f"Error: '{path}' not found", file=sys.stderr)
            return

        if not stat.S_ISDIR(inode['i_mode']):
            self.extract_file(path, dest)
            return

        dirname = path.rstrip('/').split('/')[-1] or 'root'
        if dest is None:
            dest = dirname
        elif os.path.isdir(dest):
            dest = os.path.join(dest, dirname)

        os.makedirs(dest, exist_ok=True)

        entries = self.list_dir(nid)
        for name, ino, ft in entries:
            if name in ('.', '..'):
                continue

            child_path = f"{path.rstrip('/')}/{name}"
            child_dest = os.path.join(dest, name)

            if ft == FT_DIR:
                self.extract_dir(child_path, child_dest)
            elif ft == FT_SYMLINK:
                try:
                    target = self.read_file(ino, max_size=4096).decode('utf-8', errors='replace')
                    if os.path.exists(child_dest) or os.path.islink(child_dest):
                        os.unlink(child_dest)
                    os.symlink(target, child_dest)
                    print(f"Symlink: {child_path} -> {target}")
                except Exception as e:
                    print(f"Warning: could not create symlink {child_path}: {e}", file=sys.stderr)
            else:
                try:
                    data = self.read_file(ino)
                    with open(child_dest, 'wb') as out:
                        out.write(data)
                    print(f"Extracted: {child_path} ({len(data)} bytes)")
                except Exception as e:
                    print(f"Warning: could not extract {child_path}: {e}", file=sys.stderr)

    def find_files(self, pattern, path='/', results=None):
        """Find files matching a glob pattern."""
        if results is None:
            results = []

        nid, inode = self.resolve_path(path)
        if inode is None:
            return results

        if not stat.S_ISDIR(inode['i_mode']):
            return results

        entries = self.list_dir(nid)
        for name, ino, ft in entries:
            if name in ('.', '..'):
                continue

            child_path = f"{path.rstrip('/')}/{name}"

            if fnmatch.fnmatch(name, pattern) or fnmatch.fnmatch(name.lower(), pattern.lower()):
                type_str = FILE_TYPE_NAMES.get(ft, '?')
                child_inode = self.get_inode(ino)
                size = child_inode['i_size'] if child_inode else 0
                results.append((child_path, type_str, size))

            if ft == FT_DIR:
                self.find_files(pattern, child_path, results)

        return results


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    image_path = sys.argv[1]
    command = sys.argv[2] if len(sys.argv) > 2 else 'info'
    args = sys.argv[3:]

    if not os.path.exists(image_path):
        print(f"Error: '{image_path}' not found")
        sys.exit(1)

    try:
        reader = F2FSReader(image_path)
    except Exception as e:
        print(f"Error opening image: {e}")
        sys.exit(1)

    try:
        if command == 'info':
            reader.print_info()

        elif command == 'ls':
            path = args[0] if args else '/'
            reader.print_ls(path)

        elif command == 'tree':
            path = args[0] if args else '/'
            depth = int(args[1]) if len(args) > 1 else 3
            reader.print_tree(path, depth)

        elif command == 'cat':
            if not args:
                print("Usage: fuck_f2fs.py <image> cat <path>")
                sys.exit(1)
            reader.cat_file(args[0])

        elif command == 'extract':
            if not args:
                print("Usage: fuck_f2fs.py <image> extract <path> [dest]")
                sys.exit(1)
            dest = args[1] if len(args) > 1 else None
            reader.extract_file(args[0], dest)

        elif command == 'extractdir':
            if not args:
                print("Usage: fuck_f2fs.py <image> extractdir <path> [dest]")
                sys.exit(1)
            dest = args[1] if len(args) > 1 else None
            reader.extract_dir(args[0], dest)

        elif command == 'find':
            if not args:
                print("Usage: fuck_f2fs.py <image> find <pattern>")
                sys.exit(1)
            results = reader.find_files(args[0])
            if not results:
                print("No matches found.")
            else:
                for fpath, ftype, fsize in sorted(results):
                    print(f"  {ftype} {fsize:>10d}  {fpath}")

        elif command == 'debug':
            if not args:
                # Debug root inode
                nid = reader.sb['root_ino']
            else:
                try:
                    nid = int(args[0])
                except ValueError:
                    # Treat as path, resolve to nid
                    nid, _ = reader.resolve_path(args[0])
                    if nid is None:
                        print(f"Path '{args[0]}' not found")
                        sys.exit(1)
            reader.debug_nid(nid)

        elif command == 'hexdump':
            # Dump raw block for debugging
            if not args:
                print("Usage: fuck_f2fs.py <image> hexdump <block_addr> [bytes]")
                sys.exit(1)
            blkaddr = int(args[0])
            nbytes = int(args[1]) if len(args) > 1 else 256
            data = reader._read_block(blkaddr)
            for i in range(0, min(nbytes, len(data)), 16):
                hex_part = ' '.join(f'{b:02x}' for b in data[i:i+16])
                ascii_part = ''.join(chr(b) if 32 <= b < 127 else '.' for b in data[i:i+16])
                print(f"  {i:04x}: {hex_part:<48s} {ascii_part}")

        elif command == 'cp':
            # Dump checkpoint info
            print(f"Checkpoint Info")
            print(f"{'=' * 50}")
            for k, v in reader.cp.items():
                print(f"  {k}: {v}")
            if reader.nat_bitmap:
                print(f"  NAT bitmap size: {len(reader.nat_bitmap)} bytes")
                first_bytes = ' '.join(f'{b:02x}' for b in reader.nat_bitmap[:32])
                print(f"  NAT bitmap (first 32): {first_bytes}")
            else:
                print(f"  NAT bitmap: NOT LOADED")

        else:
            print(f"Unknown command: {command}")
            print(__doc__)
            sys.exit(1)

    except KeyboardInterrupt:
        print("\nInterrupted.")
    except BrokenPipeError:
        pass
    finally:
        reader.close()


if __name__ == '__main__':
    main()

