use crate::{L3Value, LOG2_VALUE_BITS, LOG2_VALUE_BYTES, TAG_REGISTER_FRAME};

#[macro_export]
macro_rules! debug_println {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
            println!($($arg)*);
        }
    };
}


const MAX_TAG : L3Value = 0xFF;
const TAG_NONE : L3Value = 0x1F; //TODO HOW TO CHOSE THE VALUES OF THE TAGS

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
            //top_frame_start: 0, 

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
    fn add_block_to_free_list(&mut self, block: usize) {
        debug_assert!(self.is_index_valid(block), "invalid block index: {}", block);
        let header = block - HEADER_SIZE;

        let size = self.block_size(block);
        debug_assert!(block + (size as usize) <= self.content.len(), "block + size: {} + {} < {}", block, size, self.content.len());
        debug_assert!(size >= 0);
        let free_list_index = self.get_index_free_list(size as usize);

        let next_header = self.free_lists[free_list_index];
        self.set_next_free_block(block, next_header);
        self.free_lists[free_list_index] = (header) as usize;
    }


    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        //NEW -- create the free lists, and add the first block to the free list
        //       according to the size of the block

        // get size of heap

        let bitmap_size = (self.content.len() - heap_start_index  + 32) / 33;
        self.bitmap_start = heap_start_index;
        self.heap_start = heap_start_index + bitmap_size;

        debug_println!("Bitmap start at index: {} and end at: {}", self.bitmap_start, self.heap_start - 1);


        debug_println!("Heap start index: {} and end at {}", self.heap_start, self.content.len() - 1);
        let heap_size = self.content.len() - self.heap_start - HEADER_SIZE;
        let block = self.heap_start + HEADER_SIZE;
        // set the heap start
        self.set_block_header(block, TAG_NONE, heap_size); // which TAG

        //self.add_block_to_free_list(block, heap_size);
        self.add_block_to_free_list(block);
    }


    /// NEW
    /// Split the block into two blocks, the first one with size `size` and the second one with the rest
    /// Return true if the block was split, false otherwise
    fn can_split_block(&mut self, header: usize, size: usize)-> bool {
        let block = header + HEADER_SIZE;
        debug_assert!(self.is_index_valid(block) && size < MAX_BLOCK_SIZE);
        let block_size = self.block_size(block);
        debug_assert!(block_size >= 0);

        if block_size as usize == size {
            return false;
        }

        let block_size = block_size as usize;
        debug_assert!(block_size > size, "block size: {}, size: {}", block_size, size);
        let new_size = block_size - size - HEADER_SIZE;
        if (new_size as usize) > MIN_BLOCK_SIZE  {
            debug_println!("Splitting block of size: {} into blocks of size: {} and {}", block_size, size, new_size);
            let new_block = (block + size + HEADER_SIZE) as usize;
            debug_assert!(new_size > 0);
            self.set_block_header(new_block, self.block_tag(block), (new_size) as usize);
            debug_assert!(self.block_size(new_block) as usize+ size + HEADER_SIZE == block_size);
            self.add_block_to_free_list(new_block);
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
                debug_assert!(self.is_index_valid(block));
                let block_size = self.block_size(block);
                debug_assert!(block_size >= 0);
                let block_size = block_size as usize;

                //first fit
                if block_size >= size {
                    //remove header from the free list
                    if last_header == 0 {
                        self.free_lists[free_list_index] = self.get_next_free_header(block);
                    } else {
                        let next_header = self.get_next_free_header(block);
                        let last_block = last_header + HEADER_SIZE;
                        self.set_next_free_block(last_block, next_header);
                    }

                    debug_println!("Found block of size: {} in end of freelists", block_size);
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
                let block = header + HEADER_SIZE;
                debug_println!("Found block of size: {} in free list {}", self.block_size(block), free_list_index);
                debug_assert!(self.is_index_valid(block));
                self.free_lists[free_list_index] = self.get_next_free_header(block);
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
                    let block = header + HEADER_SIZE;
                    // if the block can be split, split it
                    if self.can_split_block(header, size) {
                        return Some((block, size));
                    } else {
                        let block = header + HEADER_SIZE;
                        let block_size = self.block_size(block) as usize;
                        return Some((block, block_size));
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
    pub fn allocate(&mut self, tag: L3Value, size: L3Value, root: usize)
        -> usize {
            if 0 > tag || tag > 0xFF {
                //print tag in hex
                debug_println!("Tag out of range: {:#x}", tag);
            }
            debug_assert!(0 <= tag && tag <= 0xFF, "tag: {}", tag);
            debug_assert!(0 <= size);
            debug_println!("Heap start at index: {}", self.heap_start);
            debug_println!("Heap end at index: {}", self.content.len() - 1);
            debug_println!("Allocating block of size: {}", size);
            let mut attempt = 0;
            let mut m_block = None;


            while attempt < 2 && m_block.is_none() {

                m_block = match self.find_next_free_block(size as usize) {
                    Some((block, new_size)) => {
                        debug_println!("Block found at index: {} of size {}", block, new_size);
                        self.set_block_header(block, tag, new_size as usize);
                        //let index = self.addr_to_index(block);
                        let (bmp_addr, bmp_entry_index) = self.block_index_to_bitmap_addr(block);
                        self.mark_block(bmp_addr, bmp_entry_index);
                        debug_println!("Allocated block at index: {} of size {}", block, new_size);
                        Some(block)
                    },
                    None => {
                        if attempt == 0 {
                            self.mark(root);
                            self.sweep();

                        }   
                        attempt += 1;
                        //None
                        debug_println!("Memory full for the first time");
                        None

                    }

                };
            };

            match m_block {
                Some(block) => {
                    let size = self.block_size(block) as usize;
                    //not out of bounds
                    if size + block >= self.content.len() {
                        debug_println!("Block allocated at index: {} of size {} not possible", block, size);
                    }
                    debug_assert!(size+block <= self.content.len(), "size + block: {} + {} < {}", size, block, self.content.len());
                    block
                },
                None => panic!("Out of memory")
            }
        }

    pub fn copy(&mut self, block: usize, root: usize) -> usize {
        debug_println!("Method copy is called");
        let size = self.block_size(block);
        let copy = self.allocate(self.block_tag(block), size, root);
        for i in 0..(size as usize) { self[copy + i] = self[block + i] };
        debug_println!("block copied from index {} to index {}", copy, copy +(size as usize)-1);
        copy
    }

    /// NEW 
    /// coalesce blocks if possible
    /// check if the block0 and block1 are adjacent
    /// block0 and block1 are not freed yet
    /// must check beforehand that the two blocks must be freed
    /// must call coalesce in loop until no more coalescing is possible
    /// and then free the initial block
    fn coalesce(&mut self, block0:usize, block1:usize) -> usize {
        let block0_size = self.block_size(block0);
        let block1_size = self.block_size(block1);
        debug_assert!(block0_size >= 0 && block1_size >= 0);
        let block0_end = (block0)+ (block0_size as usize) + HEADER_SIZE;
        //assert that the two blocks are adjacent
        debug_assert!(block0_end == block1);
        let new_size = (block0_size as usize) + (block1_size as usize) + HEADER_SIZE;
        self.set_block_header(block0, self.block_tag(block0), new_size as usize);
        block0
    }


    pub fn free(&mut self, block: usize) {
        debug_assert!(self.is_index_valid(block));
        
        // add the block to the free list
        self.add_block_to_free_list(block);
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

        let top_frame_0 = self.bitmap_start - 258;
        let top_frame_1 = top_frame_0 - 259;



        // READ ROOTS PARAGRAPH IN ASSIGNMENT
        let top_frame_2 = self[root + 1];
        if self.is_addr_aligned(top_frame_2){
            let top_frame_index = self.addr_to_index(top_frame_2);
            if self.is_index_valid(top_frame_index) && self.block_tag(top_frame_index) == TAG_REGISTER_FRAME {
                debug_assert!(top_frame_index == top_frame_0 || top_frame_index == top_frame_1);
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

    fn sweep(&mut self) {
        let start = self.heap_start + HEADER_SIZE;
        let end = self.content.len();
        let mut current = start;
        let mut prev: Option<usize> = None;

        // Clear previous free lists
        for i in 0..SIZE_FREE_LISTS {
            self.free_lists[i] = 0;
        }

        debug_println!("Sweeping");
        while current < end {
            let tag = self.block_tag(current);
            let mut size = self.block_size(current) as usize;
            let (bmp_addr, bmp_entry_index) = self.block_index_to_bitmap_addr(current);
            debug_println!("Sweeping block at index: {} and size {}", current, size);

            if tag != TAG_NONE && !self.is_marked(bmp_addr, bmp_entry_index) {
                self.mark_block(bmp_addr, bmp_entry_index);

                if let Some(free_block) = prev {
                    // set memory to 0
                    for i in 0..size {
                        self[free_block + i] = 0;
                    }
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
            debug_println!("Current: {}", current);
        }
        debug_println!("End Sweeping");

        if let Some(free_block) = prev {
            self.free(free_block);
        }
    }



    // Helper functions
    // NEW
    fn addr_to_index(&mut self, addr: L3Value) -> usize {
        debug_assert!(addr & ((1 << LOG2_VALUE_BYTES) - 1) == 0,
        "invalid address: {} (16#{:x})", addr, addr);
        (addr >> LOG2_VALUE_BYTES) as usize
    }

    //NEW
    fn index_to_addr(&mut self, index: usize) -> L3Value {
        //assert that the index is between the heap start and the end of the heap
        debug_assert!(self.is_index_valid(index), "invalid index: {}", index);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_index_free_list() {
        let memory = Memory::new(1024);

        // Test for size 0
        assert_eq!(memory.get_index_free_list(0), 0);

        // Test for size within range of SIZE_FREE_LISTS
        assert_eq!(memory.get_index_free_list(1), 0);
        assert_eq!(memory.get_index_free_list(5), 4);
        assert_eq!(memory.get_index_free_list(10), 9);
        assert_eq!(memory.get_index_free_list(SIZE_FREE_LISTS), SIZE_FREE_LISTS - 1);

        // Test for size greater than SIZE_FREE_LISTS
        assert_eq!(memory.get_index_free_list(SIZE_FREE_LISTS + 1), SIZE_FREE_LISTS - 1);
        assert_eq!(memory.get_index_free_list(SIZE_FREE_LISTS + 20), SIZE_FREE_LISTS - 1);
    }

    #[test]
    fn test_add_block_to_free_list() {
        let mut memory = Memory::new(1024);
        memory.set_heap_start(10);

        let block = 50; // Example block index
        let size = 4; // Example block size
        memory.set_block_header(block, TAG_NONE, size);
        memory.add_block_to_free_list(block);

        let index = memory.get_index_free_list(size);
        assert_eq!(memory.free_lists[index], block - HEADER_SIZE);
    }

    #[test]
    fn test_free_list_contains_one_block() {
        let mut memory = Memory::new(1024);
        memory.set_heap_start(10);
        let first_free_header = memory.free_lists[SIZE_FREE_LISTS-1];
        let block = first_free_header + HEADER_SIZE;

        let block_size: usize = memory.block_size(block) as usize;

        assert_eq!(block_size, 1024 - memory.heap_start - HEADER_SIZE);
        assert_eq!(block, memory.heap_start + HEADER_SIZE);
    }




    #[test]
    fn test_find_next_free_block() {
        let mut memory = Memory::new(1024);

        let heap_start = 10;
        memory.set_heap_start(heap_start);

        let block_index = memory.heap_start +30 + HEADER_SIZE;
        memory.set_block_header(block_index, TAG_NONE, 5);
        memory.add_block_to_free_list(block_index);

        assert_eq!(memory.block_size(block_index), 5);

        let another_block_index = heap_start + HEADER_SIZE + 40; 
        memory.set_block_header(another_block_index, TAG_NONE, 7);
        memory.add_block_to_free_list(another_block_index);

        let result = memory.find_next_free_block(5);

        assert_eq!(result, Some((block_index, 5)));

        assert_eq!(memory.free_lists[memory.get_index_free_list(5)], 0);

        let result = memory.find_next_free_block(7);

        assert_eq!(result, Some((another_block_index, 7)));

        assert_eq!(memory.free_lists[memory.get_index_free_list(7)], 0);
    }




    #[test]
    fn test_allocation() {
        let mut memory = Memory::new(1024);
        memory.set_heap_start(10);

        let tag = 0x01;
        let size = 10;
        let root = 0;
        let block = memory.allocate(tag, size, root);

        assert!(block != 0);
        assert_eq!(memory.block_tag(block), tag);
        assert_eq!(memory.block_size(block), size);
    }

    #[test]
    fn test_coalesce_adjacent_blocks() {
        let mut memory = Memory::new(1024);
        memory.set_heap_start(10);

        // Allocate two adjacent blocks
        let block0 = 50 + HEADER_SIZE;
        memory.set_block_header(block0, TAG_NONE, 10);

        let block1 = block0 + 10 + HEADER_SIZE;
        memory.set_block_header(block1, TAG_NONE, 15);

        // Coalesce the two blocks
        let coalesced_block = memory.coalesce(block0, block1);

        // The coalesced block should have the combined size of the two blocks
        let block_size = memory.block_size(coalesced_block) as usize;
        assert_eq!(block_size, 10 + 15 + HEADER_SIZE);
    }

    #[test]
    #[should_panic]
    fn test_coalesce_non_adjacent_blocks() {
        let mut memory = Memory::new(1024);
        memory.set_heap_start(10);

        // Allocate two non-adjacent blocks
        let block0 = 50 + HEADER_SIZE;
        memory.set_block_header(block0, TAG_NONE, 10);

        let block1 = block0 + 20 + HEADER_SIZE; // Leaving a gap
        memory.set_block_header(block1, TAG_NONE, 15);

        // Attempt to coalesce the two blocks should not be successful
        let block0_size_before = memory.block_size(block0);
        let block1_size_before = memory.block_size(block1);

        memory.coalesce(block0, block1);

        assert_eq!(memory.block_size(block0), block0_size_before);
        assert_eq!(memory.block_size(block1), block1_size_before);
    }

    #[test]
    fn test_coalesce_with_three_blocks() {
        let mut memory = Memory::new(1024);
        memory.set_heap_start(10);

        // Allocate three adjacent blocks
        let block0 = 10 + HEADER_SIZE;
        memory.set_block_header(block0, TAG_NONE, 10);

        let block1 = block0 + 10 + HEADER_SIZE;
        memory.set_block_header(block1, TAG_NONE, 15);

        let block2 = block1 + 15 + HEADER_SIZE;
        memory.set_block_header(block2, TAG_NONE, 20);

        // Coalesce the first two blocks
        let coalesced_block_1_2 = memory.coalesce(block0, block1);

        // Coalesce the resulting block with the third block
        let coalesced_block_1_2_3 = memory.coalesce(coalesced_block_1_2, block2);

        // The coalesced block should have the combined size of the three blocks
        let block_size = memory.block_size(coalesced_block_1_2_3) as usize;
        assert_eq!(block_size, 10 + 15 + 20 + 2 * HEADER_SIZE);
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
