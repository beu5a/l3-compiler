use crate::{ L3Value, LOG2_VALUE_BITS, LOG2_VALUE_BYTES, TAG_REGISTER_FRAME, TAG_NONE, MAX_TAG };

#[macro_export]
macro_rules! debug_println {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
            println!($($arg)*);
        }
    };
}

const TOP_FRAME_0_OFFSET: usize = 258;
const TOP_FRAME_1_OFFSET: usize = 258 + 259;

const HEADER_SIZE: usize = 1;
const MAX_BLOCK_SIZE: usize = 0xff_ffff;
const MIN_BLOCK_SIZE: usize = 2;

const SIZE_FREE_LISTS: usize = 32;

type FreeList = usize;

pub struct Memory {
    content: Vec<L3Value>,
    bitmap_start: usize,
    heap_start: usize,
    free_lists: [FreeList; SIZE_FREE_LISTS],
}

fn addr_to_ix(addr: L3Value) -> usize {
    (addr >> LOG2_VALUE_BYTES) as usize
}

fn ix_to_addr(ix: usize) -> L3Value {
    (ix << LOG2_VALUE_BYTES) as L3Value
}

impl Memory {
    pub fn new(word_size: usize) -> Memory {
        Memory {
            content: vec![0; word_size],
            bitmap_start: 0,
            heap_start: 0,
            free_lists: [0; SIZE_FREE_LISTS],
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        let bitmap_size = (self.content.len() - heap_start_index + 32) / 33;
        self.bitmap_start = heap_start_index;
        self.heap_start = heap_start_index + bitmap_size + HEADER_SIZE;

        let heap_size = self.content.len() - self.heap_start;
        let block = self.heap_start;

        // set the heap start
        self.set_block_header(block, TAG_NONE, heap_size);
        self.add_block_to_free_list(block);
    }

    pub fn allocate(&mut self, tag: L3Value, size: L3Value, root: usize) -> usize {
        if let Some(block) = self.try_allocate(tag, size as usize) {
            return block;
        }

        self.gc(root);

        if let Some(block) = self.try_allocate(tag, size as usize) {
            return block;
        }

        panic!("Memory allocation failed! Running out of memory!");
    }

    pub fn copy(&mut self, block: usize, root: usize) -> usize {
        let size = self.block_size(block);
        let copy = self.allocate(self.block_tag(block), size, root);
        for i in 0..size as usize {
            self[copy + i] = self[block + i];
        }
        copy
    }

    pub fn free(&mut self, block: usize) {
        let (bmp_addr, bmp_entry_index) = self.block_ix_to_bitmap_addr(block);
        if self.is_marked(bmp_addr, bmp_entry_index) {
            self.unmark_block(bmp_addr, bmp_entry_index);
        }

        let size = self.block_size(block) as usize;

        for i in 0..size {
            self[block + i] = 0;
        }

        self.set_block_header(block, TAG_NONE, size);
        self.add_block_to_free_list(block);
    }

    pub fn block_tag(&self, block: usize) -> L3Value {
        (self[block - HEADER_SIZE] >> 24) & MAX_TAG
    }

    pub fn block_size(&self, block: usize) -> L3Value {
        self[block - HEADER_SIZE] & (MAX_BLOCK_SIZE as L3Value)
    }

    pub fn set_block_header(&mut self, block: usize, tag: L3Value, size: usize) {
        self[block - HEADER_SIZE] = (tag << 24) | (size as L3Value);
    }

    // ---------------------------------------------------------HELPER FUNCTIONS ---------------------------------------------------------

    /* Free Lists helper functions :
     * 1. set_next_free_block
     * 2. get_next_free_header
     * 3. get_index_free_list
     * 4. add_block_to_free_list
     * 5. can_split_block
     * 6. get_header_from_free_list
     * 7. find_next_free_block
     * 8. coalesce
     * 9. try_allocate
     */

    fn set_next_free_block(&mut self, block: usize, next_header: usize) {
        if next_header == 0 {
            self[block] = 0;
        } else {
            self[block] = ix_to_addr(next_header);
        }
    }

    fn get_next_free_header(&mut self, block: usize) -> usize {
        let next_header = self[block];
        if next_header == 0 {
            return 0;
        } else {
            addr_to_ix(next_header)
        }
    }

    fn get_index_free_list(&self, size: usize) -> usize {
        if size == 0 {
            0
        } else {
            if size >= SIZE_FREE_LISTS - 1 { SIZE_FREE_LISTS - 1 } else { size - 1 }
        }
    }

    fn add_block_to_free_list(&mut self, block: usize) {
        let header = block - HEADER_SIZE;

        let size = self.block_size(block);
        let free_list_index = self.get_index_free_list(size as usize);

        let next_header = self.free_lists[free_list_index];
        self.set_next_free_block(block, next_header);
        self.free_lists[free_list_index] = header as usize;
    }

    fn can_split_block(&mut self, header: usize, size: usize) -> bool {
        let block = header + HEADER_SIZE;
        let block_size = self.block_size(block);

        if (block_size as usize) == size {
            return false;
        }

        let block_size = block_size as usize;
        let new_size = block_size - size - HEADER_SIZE;
        if (new_size as usize) > 0 {
            let new_block = (block + size + HEADER_SIZE) as usize;
            self.set_block_header(new_block, self.block_tag(block), new_size as usize);
            self.add_block_to_free_list(new_block);
            true
        } else {
            panic!("Block size too small to split, new size is {}", new_size);
        }
    }

    fn get_header_from_free_list(&mut self, free_list_index: usize, size: usize) -> Option<usize> {
        if free_list_index == SIZE_FREE_LISTS - 1 {
            self.find_first_fit(size)
        } else {
            let header = self.free_lists[free_list_index];
            if header == 0 {
                None
            } else {
                let block = header + HEADER_SIZE;
                if self.block_size(block) as usize >= size + MIN_BLOCK_SIZE {
                    self.free_lists[free_list_index] = self.get_next_free_header(block);
                    Some(header)
                } else {
                    None
                }
            }
        }
    }

    fn find_first_fit(&mut self, size: usize) -> Option<usize> {
        let free_list_index = SIZE_FREE_LISTS - 1;
        let mut header = self.free_lists[free_list_index];
        let mut last_header = 0;

        while header != 0 {
            let block = header + HEADER_SIZE;
            let block_size = self.block_size(block) as usize;

            if block_size >= size + MIN_BLOCK_SIZE {
                if last_header == 0 {
                    self.free_lists[free_list_index] = self.get_next_free_header(block);
                } else {
                    let next_header = self.get_next_free_header(block);
                    let last_block = last_header + HEADER_SIZE;
                    self.set_next_free_block(last_block, next_header);
                }
                return Some(header);
            }
            last_header = header;
            header = self.get_next_free_header(block);
        }
        None
    }

    fn find_next_free_block(&mut self, size: usize) -> Option<(usize, usize)> {
        let mut free_list_index = self.get_index_free_list(size);

        while free_list_index < SIZE_FREE_LISTS {
            let header = self.get_header_from_free_list(free_list_index, size);
            match header {
                Some(header) => {
                    let block = header + HEADER_SIZE;
                    // if the block can be split, split it
                    if self.can_split_block(header, size) {
                        return Some((block, size));
                    } else {
                        let block = header + HEADER_SIZE;
                        let block_size = self.block_size(block) as usize;
                        return Some((block, block_size));
                    }
                }
                None => {
                    free_list_index += 1;
                }
            }
        }
        None
    }

    fn coalesce(&mut self, block0: usize, block1: usize) -> usize {
        let block0_size = self.block_size(block0);
        let block1_size = self.block_size(block1);
        let new_size = (block0_size as usize) + (block1_size as usize) + HEADER_SIZE;
        self.set_block_header(block0, self.block_tag(block0), new_size as usize);
        block0
    }

    fn try_allocate(&mut self, tag: L3Value, size: usize) -> Option<usize> {
        if let Some((block, new_size)) = self.find_next_free_block(size) {
            self.set_block_header(block, tag, new_size as usize);
            let (bmp_addr, bmp_entry_index) = self.block_ix_to_bitmap_addr(block);
            self.mark_block(bmp_addr, bmp_entry_index);
            Some(block)
        } else {
            None
        }
    }

    /*
     * Garbage Collection helper functions:
     * 1. mark
     * 2. sweep
     * 3. gc
     */
    fn mark(&mut self, root: usize) {
        let mut stack = vec!();

        let top_frame_0 = self.bitmap_start - TOP_FRAME_0_OFFSET;
        let top_frame_1 = self.bitmap_start - TOP_FRAME_1_OFFSET;

        let idx = addr_to_ix(self[root + 1]);

        if root == top_frame_0 {
            if idx == top_frame_1 && self.block_tag(idx) == TAG_REGISTER_FRAME {
                stack.push(top_frame_1);
            }
        } else if root == top_frame_1 {
            if idx == top_frame_0 && self.block_tag(idx) == TAG_REGISTER_FRAME {
                stack.push(top_frame_0);
            }
        } else {
            panic!("Garbage Collection Error: Invalid root in mark");
        }

        stack.push(root);

        while let Some(block) = stack.pop() {
            let block_size = self.block_size(block) as usize;
            let is_top_frame = block == top_frame_0 || block == top_frame_1;

            if !self.is_ix_valid(block) && !is_top_frame {
                continue;
            }
            for i in 0..block_size {
                if !self.is_ix_valid(block + i) && !is_top_frame {
                    continue;
                }

                let addr = self[block + i];
                // verify address
                if !self.is_addr_aligned(addr) {
                    continue;
                }

                let index = addr_to_ix(addr);
                // verify index
                if !self.is_ix_valid(index) {
                    continue;
                }

                let (bmp_addr, bmp_entry_index) = self.block_ix_to_bitmap_addr(index);
                if self.is_marked(bmp_addr, bmp_entry_index) {
                    self.unmark_block(bmp_addr, bmp_entry_index);
                    stack.push(index);
                }
            }
        }
    }

    fn sweep(&mut self) {
        let start = self.heap_start;
        let end = self.content.len();
        let mut current = start;
        let mut prev: Option<usize> = None;

        // Clear previous free lists
        for i in 0..SIZE_FREE_LISTS {
            self.free_lists[i] = 0;
        }

        while current < end {
            let tag = self.block_tag(current);
            let mut size = self.block_size(current) as usize;
            let (bmp_addr, bmp_entry_index) = self.block_ix_to_bitmap_addr(current);

            if tag != TAG_NONE && !self.is_marked(bmp_addr, bmp_entry_index) {
                self.mark_block(bmp_addr, bmp_entry_index);

                if let Some(free_block) = prev {
                    self.free(free_block);
                }
                prev = None;
            } else {
                if let Some(free_block) = prev {
                    current = self.coalesce(free_block, current);
                    size = self.block_size(current) as usize;
                } else {
                    self.set_block_header(current, TAG_NONE, size);
                }
                prev = Some(current);
            }

            current += size + HEADER_SIZE;
        }

        if let Some(free_block) = prev {
            self.free(free_block);
        }
    }

    fn gc(&mut self, root: usize) {
        self.mark(root);
        self.sweep();
    }

    /*
     * Helper functions for general memory management:
     * 1. is_index_valid
     * 2. is_addr_aligned
     * 3. block_index_to_bitmap_addr
     * 4. is_marked
     * 5. mark_block
     * 6. unmark_block
     */
    fn is_ix_valid(&mut self, index: usize) -> bool {
        self.heap_start <= index && index < self.content.len()
    }

    fn is_addr_aligned(&mut self, addr: L3Value) -> bool {
        let align_mask = (1 << LOG2_VALUE_BYTES) - 1;
        let is_aligned = (addr & align_mask) == 0;
        is_aligned
    }

    fn block_ix_to_bitmap_addr(&mut self, index: usize) -> (usize, usize) {
        let bmp_offset = (index - self.heap_start) >> LOG2_VALUE_BITS;
        let mask = (1 << LOG2_VALUE_BITS) - 1;
        let bmp_entry_index = (index - self.heap_start) & mask;
        (self.bitmap_start + bmp_offset, bmp_entry_index)
    }

    fn is_marked(&mut self, bmp_addr: usize, bmp_entry_index: usize) -> bool {
        ((self[bmp_addr] >> bmp_entry_index) & 1) == 1
    }

    fn mark_block(&mut self, bmp_addr: usize, bmp_entry_index: usize) {
        let mask = 1 << bmp_entry_index;
        let to_mark = self[bmp_addr] as usize;
        self[bmp_addr] = (to_mark | mask) as L3Value;
    }

    fn unmark_block(&mut self, bmp_addr: usize, bmp_entry_index: usize) {
        let mask = !(1 << bmp_entry_index);
        let to_unmark = self[bmp_addr] as usize;
        self[bmp_addr] = (to_unmark & mask) as L3Value;
    }
}

use std::ops::{ Index, IndexMut };

impl Index<usize> for Memory {
    type Output = L3Value;
    fn index(&self, i: usize) -> &Self::Output {
        &self.content[i]
    }
}

impl IndexMut<usize> for Memory {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.content[i]
    }
}
