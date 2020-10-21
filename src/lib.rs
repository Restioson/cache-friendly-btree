#![forbid(unsafe_code)]
#![feature(const_generics, const_evaluatable_checked, const_fn)]
#![allow(incomplete_features)]
#![feature(const_panic)] // TODO dbg

use core::cmp;
use std::borrow::BorrowMut;
use std::ops::{Add, Index, IndexMut};

// Order starts from one and counts up the tree
// Level starts from one and counts down the tree
// Subtree order starts from zero and counts up the tree
// Flat tree index math based on https://opendsa-server.cs.vt.edu/ODSA/Books/Everything/html/CompleteTree.html

mod flat_tree {
    pub const fn sibling_of(index: usize) -> usize {
        if index & 1 == 0 {
            index + 1
        } else {
            index - 1
        }
    }

    pub const fn parent_of(index: usize) -> usize {
        (index - 1) >> 1
    }

    pub const fn blocks_in_tree(levels: u8) -> usize {
        ((1 << levels) - 1) as usize
    }

    pub const fn blocks_in_level(level: u8) -> usize {
        blocks_in_tree(level) - blocks_in_tree(level - 1)
    }
}

mod nested_tree {
    use crate::flat_tree::blocks_in_tree as blocks_in_flat_tree;
    pub const LEVELS_IN_SUBTREE: u8 = 6; // 2 ^ 6 - 1 = 63 ~= cache line on x86_64
    pub const SIZE_OF_SUBTREE: usize = 1 << (LEVELS_IN_SUBTREE - 1);

    pub const fn blocks_in_tree(levels_in_tree: u8) -> usize {
        let perfect_flat_levels_in_subtrees =
            (levels_in_tree / LEVELS_IN_SUBTREE) * LEVELS_IN_SUBTREE;
        let leftover_blocks = blocks_in_flat_tree(levels_in_tree)
            - blocks_in_flat_tree(perfect_flat_levels_in_subtrees);
        let blocks_in_subtrees =
            perfect_flat_levels_in_subtrees as usize * blocks_in_flat_tree(LEVELS_IN_SUBTREE);

        blocks_in_subtrees + leftover_blocks
    }
}

use crate::nested_tree::{LEVELS_IN_SUBTREE, SIZE_OF_SUBTREE};
pub use nested_tree::blocks_in_tree;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
#[repr(transparent)]
struct Block {
    /// Greatest order of free block below this block. Zero means nothing.
    order_free: u8,
}

impl Block {
    fn is_used(&self) -> bool {
        self.order_free == 0
    }
}

impl Add<u8> for Block {
    type Output = Block;

    fn add(self, rhs: u8) -> Block {
        Block {
            order_free: self.order_free + rhs,
        }
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct GlobalIndex(pub usize);

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct LocalIndex(pub usize);

impl LocalIndex {
    const fn is_root(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Copy, Clone)]
#[repr(transparent)]
struct SubtreeIndex(pub usize);

#[derive(Copy, Clone)]
#[repr(transparent)]
struct Order(pub u8);

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
struct SubtreeOrder(pub u8);

struct Tree<B, const LEVELS: u8> {
    blocks: B,
}

impl<B, const LEVELS: u8> Index<GlobalIndex> for Tree<B, LEVELS>
where
    B: BorrowMut<[Block; blocks_in_tree(LEVELS)]>,
{
    type Output = Block;

    fn index(&self, index: GlobalIndex) -> &Block {
        &self.blocks.borrow()[index.0]
    }
}

impl<B, const LEVELS: u8> IndexMut<GlobalIndex> for Tree<B, LEVELS>
where
    B: BorrowMut<[Block; blocks_in_tree(LEVELS)]>,
{
    fn index_mut(&mut self, index: GlobalIndex) -> &mut Block {
        &mut self.blocks.borrow_mut()[index.0]
    }
}

impl<B, const LEVELS: u8> Tree<B, LEVELS>
where
    B: BorrowMut<[Block; blocks_in_tree(LEVELS)]>,
{
    fn new_free(mut blocks: B) -> Self {
        let mut borrowed_blocks = blocks.borrow_mut();

        let slice_offset = Self::subtree_slice_offset(SubtreeOrder(0));
        let tree_offset_size = if LEVELS % LEVELS_IN_SUBTREE != 0 {
            (1 << ((LEVELS % LEVELS_IN_SUBTREE) - 1) - 1)
        } else {
            1 << (LEVELS_IN_SUBTREE - 2)
        };
        let bottom_level_size = borrowed_blocks.len() - slice_offset;

        for tree in 0.. {
            let tree_offset = tree_offset_size * tree;
            if tree_offset > borrowed_blocks.len() {
                break;
            }

            for i in tree_offset..bottom_level_size {
                borrowed_blocks[slice_offset + i] = Block { order_free: 1 };
            }
        }

        let mut tree = Tree { blocks };

        for j in 0.. {
            let tree_offset = tree_offset_size * j;
            if tree_offset > tree.blocks.borrow().len() {
                break;
            }

            for i in tree_offset..bottom_level_size {
                tree.update_blocks_above(GlobalIndex(slice_offset + i), Order(1));
            }
        }

        tree
    }

    /// Update all the parents of a block
    fn update_blocks_above(&mut self, mut index: GlobalIndex, order: Order) {
        // Iterate upwards and set parents accordingly
        for order in (order.0 - 1)..LEVELS {
            let order = Order(order);
            let block = self[index];
            let sibling = self[Self::sibling(index, order)];
            let parent_idx = Self::parent(index, order);
            dbg!((order.0, index, parent_idx));

            // Set the parent appropriately and carry on propagating upwards
            self.merge_from_children(parent_idx, block, sibling);
            index = parent_idx;
        }
    }

    const fn subtree_order(order: Order) -> SubtreeOrder {
        SubtreeOrder(if order.0 <= LEVELS % LEVELS_IN_SUBTREE {
            0
        } else {
            (order.0 - (LEVELS % LEVELS_IN_SUBTREE)) / LEVELS_IN_SUBTREE + 1
        })
    }

    // TODO const
    fn parent(idx: GlobalIndex, order: Order) -> GlobalIndex {
        let subtree_order = Self::subtree_order(order);
        let local_idx = Self::local_idx(idx, subtree_order);
        let subtree_idx = Self::subtree_idx(idx, subtree_order);
        dbg!(subtree_order);

        if local_idx.is_root() {
            println!("root: {:?}", local_idx);
            let parent_subtree_order = SubtreeOrder(subtree_order.0 + 1);
            let subtree_slice_offset = Self::subtree_slice_offset(subtree_order);
            let subtree_slice_idx = idx.0 - subtree_slice_offset;
            let parent_subtree_idx = SubtreeIndex(subtree_slice_idx << 1);

            Self::global_idx(LocalIndex(0), parent_subtree_idx, parent_subtree_order)
        } else {
            println!("Local");
            let parent_local = LocalIndex(flat_tree::parent_of(local_idx.0));
            Self::global_idx(parent_local, subtree_idx, subtree_order)
        }
    }

    fn sibling(idx: GlobalIndex, order: Order) -> GlobalIndex {
        let subtree_order = Self::subtree_order(order);
        let subtree_idx = Self::subtree_idx(idx, subtree_order);
        let local_idx = Self::local_idx(idx, subtree_order);

        if local_idx.is_root() {
            let sibling_subtree_idx = SubtreeIndex(flat_tree::sibling_of(subtree_idx.0));
            Self::global_idx(LocalIndex(0), sibling_subtree_idx, subtree_order)
        } else {
            let sibling_local = LocalIndex(flat_tree::sibling_of(local_idx.0));
            Self::global_idx(sibling_local, subtree_idx, subtree_order)
        }
    }

    fn subtree_slice_offset(subtree_order: SubtreeOrder) -> usize {
        if subtree_order.0 < LEVELS - 2 {
            blocks_in_tree(LEVELS - subtree_order.0 - 1)
        } else {
            0
        }
    }

    fn size_of_subtree(subtree_order: SubtreeOrder) -> usize {
        if subtree_order.0 == 0 && LEVELS % LEVELS_IN_SUBTREE != 0 {
            (1 << (LEVELS % LEVELS_IN_SUBTREE) - 1)
        } else {
            SIZE_OF_SUBTREE
        }
    }

    fn subtree_idx(idx: GlobalIndex, subtree_order: SubtreeOrder) -> SubtreeIndex {
        let subtree_slice_offset = Self::subtree_slice_offset(subtree_order);
        let subtree_slice_idx = idx.0 - subtree_slice_offset;
        SubtreeIndex(subtree_slice_idx / Self::size_of_subtree(subtree_order))
    }

    fn local_idx(idx: GlobalIndex, subtree_order: SubtreeOrder) -> LocalIndex {
        let subtree_slice_offset = Self::subtree_slice_offset(subtree_order);
        let subtree_slice_idx = idx.0 - subtree_slice_offset;
        LocalIndex(subtree_slice_idx % Self::size_of_subtree(subtree_order))
    }

    fn global_idx(
        local_idx: LocalIndex,
        subtree_idx: SubtreeIndex,
        subtree_order: SubtreeOrder,
    ) -> GlobalIndex {
        let subtree_slice_offset = Self::subtree_slice_offset(subtree_order);
        GlobalIndex(subtree_idx.0 * Self::size_of_subtree(subtree_order) + local_idx.0 + subtree_slice_offset)
    }

    fn merge_from_children(&mut self, idx: GlobalIndex, left: Block, right: Block) {
        self[idx] = if left == right && !left.is_used() {
            left + 1
        } else {
            cmp::max(left, right)
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryInto;
    use std::iter;

    fn new_flat_blocks<const N: usize>() -> Box<[Block; N]> {
        let v: Box<[Block]> = iter::repeat(Block { order_free: 1 }).take(N).collect();
        v.try_into().map_err(|_| panic!()).unwrap()
    }

    #[test]
    fn flat_tree_fns() {
        //       1
        //     2   2
        //    3 3 3 3

        assert_eq!(flat_tree::blocks_in_tree(3), 1 + 2 + 4);
        assert_eq!(flat_tree::blocks_in_tree(2), 1 + 2);
        assert_eq!(flat_tree::blocks_in_tree(1), 1);

        assert_eq!(flat_tree::blocks_in_level(1), 1);
        assert_eq!(flat_tree::blocks_in_level(2), 2);
        assert_eq!(flat_tree::blocks_in_level(3), 4);

        //       a
        //     b   c
        //    d e f g
        //
        //   0 1 2 3 4 5 6
        //   1 2 3 4 5 6 7
        // [ a b c d e f g ]
    }

    #[test]
    fn test_init_tree() {
        type TestTree = Tree<Box<[Block; blocks_in_tree(8)]>, 8>;
        let tree = TestTree::new_free(new_flat_blocks());

        // Highest level has 1 block, next has 2, next 4
        assert_eq!(tree.blocks[0].order_free, 8);

        assert_eq!(tree.blocks[1].order_free, 7);
        assert_eq!(tree.blocks[2].order_free, 7);

        assert_eq!(tree.blocks[3].order_free, 6);
        assert_eq!(tree.blocks[4].order_free, 6);
        assert_eq!(tree.blocks[5].order_free, 6);
        assert_eq!(tree.blocks[6].order_free, 6);
    }
}
