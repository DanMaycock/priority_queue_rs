use core::iter::FromIterator;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::rc::{Rc, Weak};

pub type QueueIndex = Weak<RefCell<usize>>;

pub struct QueueItem<T: PartialOrd + PartialEq> {
    entry: T,
    index: Rc<RefCell<usize>>,
}

impl<T: PartialOrd + PartialEq> QueueItem<T> {
    fn new(entry: T, index: usize) -> Self {
        QueueItem {
            entry,
            index: Rc::new(RefCell::new(index)),
        }
    }
}

impl<T: PartialOrd + PartialEq> PartialEq for QueueItem<T> {
    fn eq(&self, other: &QueueItem<T>) -> bool {
        self.entry == other.entry
    }
}

impl<T: PartialOrd + PartialEq> PartialOrd for QueueItem<T> {
    fn partial_cmp(&self, other: &QueueItem<T>) -> Option<Ordering> {
        self.entry.partial_cmp(&other.entry)
    }
}

pub struct PriorityQueue<T: PartialOrd + PartialEq> {
    queue: Vec<QueueItem<T>>,
}

fn get_parent(index: usize) -> usize {
    (index + 1) / 2 - 1
}

fn get_left(index: usize) -> usize {
    2 * (index + 1) - 1
}

fn get_right(index: usize) -> usize {
    2 * (index + 1)
}

impl<T: PartialOrd + PartialEq> PriorityQueue<T> {
    pub fn new() -> Self {
        PriorityQueue { queue: vec![] }
    }

    pub fn push(&mut self, entry: T) -> QueueIndex {
        let index = self.queue.len();
        let item = QueueItem::new(entry, index);
        let item_index = Rc::downgrade(&item.index);
        self.queue.push(item);
        self.sift_up(index);
        item_index
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.queue.is_empty() {
            None
        } else {
            self.swap(0, self.queue.len() - 1);
            let popped_event = self.queue.pop().unwrap();
            self.sift_down(0);
            Some(popped_event.entry)
        }
    }

    pub fn remove(&mut self, index: QueueIndex) {
        if let Some(index) = index.upgrade() {
            let index = *index.borrow();
            self.swap(index, self.queue.len() - 1);
            self.queue.pop();
            if index < self.queue.len() {
                self.update(index);
            }
        }
    }

    fn update(&mut self, index: usize) {
        if index > 0 && self.queue[get_parent(index)] > self.queue[index] {
            self.sift_up(index);
        } else {
            self.sift_down(index);
        }
    }

    fn sift_up(&mut self, mut index: usize) {
        while index > 0 && self.queue[get_parent(index)] > self.queue[index] {
            self.swap(index, get_parent(index));
            index = get_parent(index);
        }
    }

    fn sift_down(&mut self, mut index: usize) {
        loop {
            let mut new_index = index;
            let left = get_left(index);
            let right = get_right(index);
            if left < self.queue.len() && self.queue[new_index] > self.queue[left] {
                new_index = left;
            }
            if right < self.queue.len() && self.queue[new_index] > self.queue[right] {
                new_index = right;
            }
            if new_index != index {
                self.swap(index, new_index);
                index = new_index;
            } else {
                break;
            }
        }
    }

    fn swap(&mut self, idx_1: usize, idx_2: usize) {
        self.queue.swap(idx_1, idx_2);
        *self.queue[idx_1].index.borrow_mut() = idx_1;
        *self.queue[idx_2].index.borrow_mut() = idx_2;
    }

    /** Iterates over all items in the queue and returns the first entry that matches the given predicate */
    pub fn find<P>(&self, predicate: P) -> Option<QueueIndex>
    where
        P: Fn(&T) -> bool,
    {
        if let Some(item) = self.queue.iter().find(|item| predicate(&item.entry)) {
            Some(Rc::downgrade(&item.index))
        } else {
            None
        }
    }

    pub fn find_all<P>(&self, predicate: P) -> Vec<QueueIndex>
    where
        P: Fn(&T) -> bool,
    {
        self.queue
            .iter()
            .filter_map(|item| {
                if predicate(&item.entry) {
                    Some(Rc::downgrade(&item.index))
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn remove_all<P>(&mut self, predicate: P)
    where
        P: Fn(&T) -> bool,
    {
        let indices_to_remove = self.find_all(predicate);
        for index in indices_to_remove {
            self.remove(index);
        }
    }
}

impl<T: PartialOrd + PartialEq> FromIterator<T> for PriorityQueue<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut c = PriorityQueue::new();
        for i in iter {
            c.push(i);
        }
        c
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pop() {
        let mut events = PriorityQueue::new();
        events.push(1.0);
        events.push(2.0);
        events.push(0.5);

        assert_eq!(events.pop().unwrap(), 0.5);
        assert_eq!(events.pop().unwrap(), 1.0);
        assert_eq!(events.pop().unwrap(), 2.0);

        assert!(events.pop().is_none());
    }

    #[test]
    fn test_remove() {
        let mut queue = PriorityQueue::new();
        let index = queue.push(1.0);
        queue.push(2.0);
        queue.push(0.5);

        queue.remove(index);

        assert_eq!(queue.pop().unwrap(), 0.5);
        assert_eq!(queue.pop().unwrap(), 2.0);

        assert!(queue.pop().is_none());
    }

    #[test]
    fn test_pop_then_push() {
        let mut queue = PriorityQueue::new();

        queue.push(1.0);
        queue.push(2.0);

        assert_eq!(queue.pop().unwrap(), 1.0);

        queue.push(0.5);

        assert_eq!(queue.pop().unwrap(), 0.5);
        assert_eq!(queue.pop().unwrap(), 2.0);

        assert!(queue.pop().is_none());
    }

    #[test]
    fn test_remove_then_push() {
        let mut queue = PriorityQueue::new();

        let index = queue.push(1.0);
        queue.push(2.0);

        queue.remove(index);

        queue.push(0.5);

        assert_eq!(queue.pop().unwrap(), 0.5);
        assert_eq!(queue.pop().unwrap(), 2.0);

        assert!(queue.pop().is_none());
    }

    #[test]
    fn test_from_iterator() {
        let vec = vec![0.5, 2.0, 1.0];

        let mut queue: PriorityQueue<f64> = vec.iter().map(|&i| i).collect();

        assert_eq!(queue.pop().unwrap(), 0.5);
        assert_eq!(queue.pop().unwrap(), 1.0);
        assert_eq!(queue.pop().unwrap(), 2.0);
    }
}
