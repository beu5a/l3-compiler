use crate::{L3Value, LOG2_VALUE_BITS, LOG2_VALUE_BYTES, TAG_REGISTER_FRAME};

const MAX_TAG : L3Value = 0xFF;

const HEADER_SIZE : usize = 1;
const MAX_BLOCK_SIZE : usize = 0xFF_FFFF;

pub struct Memory {
    content: Vec<L3Value>,
    bitmap_start: usize, // NEW
    heap_start: usize, // NEW
    top_frame_start: usize, // NEW - can be removed ???
    free_ix: usize,
}


impl Memory {
    pub fn new(word_size: usize) -> Memory {
        Memory {
            content: vec![0; word_size],
            bitmap_start: 0,
            heap_start: 0, 
            top_frame_start: 0, 
            free_ix: 0
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        self.free_ix = heap_start_index
    }

    pub fn allocate(&mut self, tag: L3Value, size: L3Value, _root: usize)
                    -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);

        let block = self.free_ix + 1;
        self.free_ix = block + (size as usize);
        if self.free_ix >= self.content.len() { panic!("no more memory"); };
        self.set_block_header(block, tag, size as usize);
        block
    }

    pub fn copy(&mut self, block: usize, root: usize) -> usize {
        let size = self.block_size(block);
        let copy = self.allocate(self.block_tag(block), size, root);
        for i in 0..(size as usize) { self[copy + i] = self[block + i] };
        copy
    }

    pub fn free(&mut self, _block: usize) {
        // do nothing
    }

    pub fn block_tag(&self, block: usize) -> L3Value {
        (self[block - HEADER_SIZE] >> 24) & MAX_TAG
    }

    pub fn block_size(&self, block: usize) -> L3Value {
        self[block - HEADER_SIZE] & MAX_BLOCK_SIZE as L3Value
    }

    pub fn set_block_header(&mut self, block: usize, tag: L3Value, size: usize){
        debug_assert!(0 <= tag && tag <= MAX_TAG);
        debug_assert!(size <= MAX_BLOCK_SIZE);

        self[block - HEADER_SIZE] = (tag << 24 ) | (size as L3Value)
    }

    /* Traverse the reachability graph starting from the root block.
     * Mark all reachable blocks.
     * NEW
     */
    fn mark(&mut self, root: usize) {
        // do nothing
        let mut stack = vec![root];

        // TODO add address verification.

        // We start with all allocated blocks marked, so we can unmark them (ie set to 0)
        // Assigmnet , Bitmap, Paragraph 4
        while let Some(block) = stack.pop() {
            let block_size = self.block_size(block) as usize;
            for i in 0..block_size {
                let addr = self[block + i];
                // verify address
                let index = self.addr_to_index(addr);
                // verify index

                let (bmp_addr, bmp_entry_index) = self.block_index_to_bitmap_addr(index);

                //if reachable (and not already unmarked) add to stack
                if self.is_marked(bmp_addr, bmp_entry_index) {
                    self.unmark_block(bmp_addr, bmp_entry_index);
                    stack.push(index);
                }


            }


        }    
    }


    // Helper functions
    // NEW
    fn addr_to_index(&mut self, addr: L3Value) -> usize {
        (addr >> LOG2_VALUE_BYTES) as usize
    }
    
    //NEW
    fn index_to_addr(&mut self, index: usize) -> L3Value {
        (index << LOG2_VALUE_BYTES) as L3Value
    }
    
    //NEW
    fn block_index_to_bitmap_addr(&mut self ,index: usize) -> (usize,usize) {
        let bmp_offset = (index - self.heap_start) >> LOG2_VALUE_BITS;
        // mask is 2^LOG2_VALUE_BITS - 1
        let mask = (1 << LOG2_VALUE_BITS) - 1;
        let bmp_entry_index = (index - self.heap_start) & (mask);
        ((self.bitmap_start + bmp_offset) , bmp_entry_index)
    }


    // Check if the bitmap bit is set to 1
    // NEW
    fn is_marked(&mut self, bmp_addr: usize, bmp_entry_index: usize) -> bool {
        ((self[bmp_addr] >> bmp_entry_index) & 1) == 1

    }

    // Mark = set the bitmap bit to 1
    // NEW
    fn mark_block(&mut self, bmp_addr: usize, bmp_entry_index: usize) {
        let mask = 1 << bmp_entry_index;
        let to_mark = self[bmp_addr] as usize;
        self[bmp_addr] = (to_mark | mask) as L3Value;
    }

    // Unmark = set the bitmap bit to 0
    // NEW
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
