use crate::{L3Value, LOG2_VALUE_BITS, LOG2_VALUE_BYTES, TAG_REGISTER_FRAME};


const MAX_TAG : L3Value = 0xFF;

const HEADER_SIZE : usize = 1;
const MAX_BLOCK_SIZE : usize = 0xFF_FFFF;
const SIZE_FREE_LISTS : usize = 32; //NEW
const MIN_BLOCK_SIZE : usize = 2; //NEW - block must be greater than 2 words of the actual size
                                  //      to be split
                                  
type FreeList = usize; // NEW 

pub struct Memory {
    content: Vec<L3Value>,
    bitmap_start: usize, // NEW
    heap_start: usize, // NEW
    top_frame_start: usize, // NEW - can be removed ???
    free_lists: [FreeList; SIZE_FREE_LISTS], // NEW -- free lists is list of 32 lists 
                                             // free_lists[i] contains the index of the first block of the free list of size i+1
                                             // free_lists[0] contains the index of the first block of the free list of size 1
}


impl Memory {
    pub fn new(word_size: usize) -> Memory {
        Memory {
            content: vec![0; word_size],
            bitmap_start: 0,
            heap_start: 0, 
            top_frame_start: 0, 

            //NEW
            free_lists: [0; SIZE_FREE_LISTS],
        }
    }

    /// NEW
    /// Set the link for the next free block in the free list
    fn set_next_free_block(&mut self, block: usize, next_header: usize) {
        debug_assert!(block < self.content.len() && next_header < self.content.len());
        debug_assert!(block != 0);
        if next_header == 0 {
            self[block] = 0;
        } else {
            self[block] = self.index_to_addr(next_header);
        }
    }

    /// NEW
    /// Get the next free block in the free list
    fn get_next_free_header(&mut self, block: usize) -> usize {
        let next_header = self[block];
        if next_header == 0 {
            return 0; 
        } else {
            self.addr_to_index(next_header)
        }
    }

    /// NEW
    /// Get the index of the free list according to the size of the block
    fn get_index_free_list(&self, size: usize) -> usize {
        if size == 0 {
            0
        } else {
            if size >= SIZE_FREE_LISTS - 1 {
                SIZE_FREE_LISTS - 1
            } else {
                size - 1
            }
        }

    }


    /// NEW
    /// Add block in the free list according to the size of the block
    fn add_block_to_free_list(&mut self, block: usize, size: usize) {
        debug_assert!(block < self.content.len() && (size)  < MAX_BLOCK_SIZE);

        let free_list_index = self.get_index_free_list(size);

        let next_header = self.free_lists[free_list_index];
        self.set_next_free_block(block, next_header);
        self.free_lists[free_list_index] = (block-HEADER_SIZE) as usize;
    }


    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        //NEW -- create the free lists, and add the first block to the free list
        //       according to the size of the block

        // get size of heap
        let heap_size = self.content.len() - heap_start_index;
        let block = heap_start_index + HEADER_SIZE;
        // set the heap start
        self.set_block_header(block, 0, heap_size);

        self.add_block_to_free_list(block, heap_size);
    }


    /// NEW
    /// Split the block into two blocks, the first one with size `size` and the second one with the rest
    /// Return true if the block was split, false otherwise
    fn can_split_block(&mut self, block: usize, size: usize)-> bool {
        let block_size = self.block_size(block);
        debug_assert!(block_size >= 0);

        let block_size = block_size as usize;
        debug_assert!(block_size >= size);
        let new_size = block_size - size;
        if (new_size as usize) > MIN_BLOCK_SIZE  {
            let new_block = (block + size + HEADER_SIZE) as usize;
            self.set_block_header(new_block, self.block_tag(block), new_size as usize);
            self.add_block_to_free_list(new_block, new_size);
            true
        }else { 
            false
        }
    }

    ///NEW
    /// Get the header from the free list
    fn get_header_from_free_list(&mut self, free_list_index: usize, size:usize) -> Option<usize> {
        debug_assert!(free_list_index < SIZE_FREE_LISTS);
        debug_assert!( size < MAX_BLOCK_SIZE);
        // get the block from the free list
        // if the free list is empty, return None
        // if size is greater than 32, iterate over the free lists until a block of the right size is found
        //
        if free_list_index == (SIZE_FREE_LISTS -1) {
            let mut header = self.free_lists[free_list_index];
            let mut last_header = 0;
            while header != 0 {
                let block = header + HEADER_SIZE;
                let block_size = self.block_size(block);
                debug_assert!(block_size >= 0);
                let block_size = block_size as usize;

                //first fit
                if block_size >= size {
                    //remove header from the free list
                    if last_header == 0 {
                        self.free_lists[free_list_index] = self.get_next_free_header(header);
                    } else {
                        let next_header = self.get_next_free_header(header);
                        self.set_next_free_block(last_header, next_header);
                    }

                    return Some(header);
                }
                last_header = header;
                header = self.get_next_free_header(block);
            }
            return None
        } else {
            let header = self.free_lists[free_list_index];
            if header == 0 {
                return None;
            } else {
                //remove header from the free list
                self.free_lists[free_list_index] = self.get_next_free_header(header);
                return Some(header);
            }
        }
    }

    /// NEW
    /// Find the next free block of size `size` and return the block index and the new size of the block
    /// If no block is found, return None
    /// Can modify the size if needed 
    fn find_next_free_block(&mut self, size:usize) -> Option<(usize, usize)> {
        // find the index of the free list that can hold the block
        let mut free_list_index = self.get_index_free_list(size); 

        while free_list_index < SIZE_FREE_LISTS {
            let header = self.get_header_from_free_list(free_list_index, size);
            match header {
                Some(header) => {
                    // if the block can be split, split it
                    if self.can_split_block(header, size) {
                        return Some((header, size));
                    } else {
                        let block_size = self.block_size(header) as usize;
                        return Some((header, block_size));
                    }
                },
                None => {
                    free_list_index += 1;
                }
            }
        }
        None

    }

    /// allocate a block of size `size` with tag `tag` and return the block index
    pub fn allocate(&mut self, tag: L3Value, size: L3Value, _root: usize)
                    -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);

        match self.find_next_free_block(size as usize) {
            Some((block, new_size)) => {
                self.set_block_header(block, tag, new_size as usize);
                // set the bitmap bit to 1
                let index = self.addr_to_index(self[block]); 
                let (bmp_addr, bmp_entry_index) = self.block_index_to_bitmap_addr(index);
                self.mark_block(bmp_addr,bmp_entry_index);  
                block
            },
            None => panic!("no more memory")
        }

    }

    pub fn copy(&mut self, block: usize, root: usize) -> usize {
        let size = self.block_size(block);
        let copy = self.allocate(self.block_tag(block), size, root);
        for i in 0..(size as usize) { self[copy + i] = self[block + i] };
        copy
    }

    /// NEW 
    /// coalesce blocks if possible
    /// check if the block0 and block1 are adjacent
    /// block0 and block1 are not freed yet
    /// must check beforehand that the two blocks must be freed
    /// must call coalesce in loop until no more coalescing is possible
    /// and then free the initial block
    fn coalesce(&mut self, block0:usize, block1:usize) -> bool {
        let block0_size = self.block_size(block0);
        let block1_size = self.block_size(block1);
        debug_assert!(block0_size >= 0 && block1_size >= 0);
        let block0_end = (block0)+ (block0_size as usize) + HEADER_SIZE;
        if block0_end == block1 {
            let new_size = (block0_size as usize) + (block1_size as usize) + HEADER_SIZE;
            self.set_block_header(block0, self.block_tag(block0), new_size as usize);
            return true;
        }
        false
    }


    pub fn free(&mut self, block: usize) {
        //TODO: check that the block is valid and allocated

        
        //let index = self.addr_to_index(self[block]);
        //let (bmp_addr, bmp_entry_index) = self.block_index_to_bitmap_addr(index);
        //self.unmark_block(bmp_addr, bmp_entry_index);

        // add the block to the free list
        self.add_block_to_free_list(block, self.block_size(block) as usize);
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

        // READ ROOTS PARAGRAPH IN ASSIGNMENT
        let top_frame_2 = self[root + 1];
        if self.is_addr_aligned(top_frame_2){
            let top_frame_index = self.addr_to_index(top_frame_2);
            if self.is_index_valid(top_frame_index) && self.block_tag(top_frame_index) == TAG_REGISTER_FRAME {
                stack.push(top_frame_index);
            }
        }


        // We start with all allocated blocks marked, so we can unmark them (ie set to 0)
        // Assigmnet , Bitmap, Paragraph 4
        while let Some(block) = stack.pop() {
            let block_size = self.block_size(block) as usize;
            for i in 0..block_size {

                let addr = self[block + i];
                // verify address
                if ! self.is_addr_aligned(addr) {
                    continue;
                }

                let index = self.addr_to_index(addr);
                // verify index
                if ! self.is_index_valid(index) {
                    continue;
                }
                

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

    /* checks if the index is within the bounds of the heap 
    */
    fn is_index_valid(&mut self, index: usize) -> bool {
        self.heap_start < index && index < self.content.len()
    }

    /* The expression (addr & ((1 << LOG2_VALUE_BYTES) - 1)) == 0 checks if addr is aligned to a 
        boundary of 2^LOG2_VALUE_BYTES bytes. It does this by creating a bitmask with the lower LOG2_VALUE_BYTES bits set to 1, 
        then using a bitwise AND operation to see if these bits in addr are all zero. If they are
    */
    fn is_addr_aligned(&mut self, addr: L3Value) -> bool {
        let align_mask = (1 << LOG2_VALUE_BYTES) - 1;
        let is_aligned = (addr & align_mask) == 0;
        is_aligned        
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
