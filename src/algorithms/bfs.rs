use crate::data_structures::{bitvec::FastBitvec, graph::Graph};
use std::collections::VecDeque;

pub trait GraphLike {
    fn neighbors(&self, node: usize) -> Vec<usize>;
    fn get_nodes(&self) -> Vec<usize>;
}
/// An iterator iterating over nodes of a graph in a breadth-first-search order
pub struct StandardBFS<'a> {
    start: Option<usize>,
    graph: &'a Graph,
    visited: &'a mut FastBitvec,
    queue: VecDeque<usize>,
    max_depth: Option<usize>,
    already_visited: usize,
}

impl<'a> Iterator for StandardBFS<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start.is_some() {
            self.visited.set(self.start.unwrap(), true);
            self.queue.push_back(self.start.unwrap());
            self.start = None;
        }

        if self.queue.is_empty() {
            return None;
        }
        let temp = self.queue.pop_front().unwrap();
        self.already_visited += 1;

        if self.max_depth.is_none()
            || self.already_visited + self.queue.len() < self.max_depth.unwrap()
        {
            let neighbors = self.graph.neighbors(temp);
            let needed_elements = if self.max_depth.is_none() {
                neighbors.len()
            } else {
                let x = self.max_depth.unwrap() - self.already_visited - self.queue.len();
                if x > neighbors.len() {
                    neighbors.len()
                } else {
                    x
                }
            };

            let neighbors: Vec<usize> = neighbors
                .iter()
                .filter(|n| !self.visited.get(**n))
                .take(needed_elements)
                .copied()
                .collect();

            for n in neighbors {
                self.visited.set(n, true);
                self.queue.push_back(n);
            }
        }

        Some(temp)
    }
}

impl<'a> StandardBFS<'a> {
    /// Returns a new Standard BFS iterator. Takes a reference to a graph and a starting node.
    ///
    /// Time complexity for the entire BFS: O(n)
    /// # Example
    /// ```
    /// use star::algorithms::bfs::StandardBFS;
    /// use star::data_structures::graph::Graph;
    /// use star::data_structures::bitvec::FastBitvec;
    /// let graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///     ],
    /// );
    ///
    ///  StandardBFS::new(&graph, 0, &mut FastBitvec::new(graph.nodes));
    /// ```

    pub fn new(graph: &'a Graph, start: usize, visited: &'a mut FastBitvec) -> Self {
        Self {
            start: Some(start),
            graph,
            queue: VecDeque::new(),
            visited,
            max_depth: None,
            already_visited: 0,
        }
    }

    pub fn new_with_depth(
        graph: &'a Graph,
        start: usize,
        visited: &'a mut FastBitvec,
        depth: usize,
    ) -> Self {
        Self {
            start: Some(start),
            graph,
            queue: VecDeque::new(),
            visited,
            max_depth: Some(depth),
            already_visited: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        algorithms::bfs::StandardBFS,
        data_structures::{bitvec::FastBitvec, graph::Graph},
    };

    #[test]
    fn test_whole() {
        let graph = Graph::new_with_edges(
            6,
            vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        );

        assert_eq!(
            StandardBFS::new(&graph, 0, &mut FastBitvec::new(graph.nodes)).collect::<Vec<usize>>(),
            [0, 3, 2, 1, 4]
        );
    }

    #[test]
    fn test_whole_other_start() {
        let graph = Graph::new_with_edges(
            6,
            vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        );

        assert_eq!(
            StandardBFS::new(&graph, 2, &mut FastBitvec::new(graph.nodes)).collect::<Vec<usize>>(),
            [2, 0, 1, 3, 4]
        );
    }

    #[test]
    fn test_whole_with_max_depth() {
        let graph = Graph::new_with_edges(
            6,
            vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        );

        assert_eq!(
            StandardBFS::new_with_depth(&graph, 0, &mut FastBitvec::new(graph.nodes), 3)
                .collect::<Vec<usize>>(),
            [0, 3, 2]
        );
    }

    #[test]
    fn test_whole_other_start_with_max_depth() {
        let graph = Graph::new_with_edges(
            6,
            vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        );

        assert_eq!(
            StandardBFS::new_with_depth(&graph, 2, &mut FastBitvec::new(graph.nodes), 3)
                .collect::<Vec<usize>>(),
            [2, 0, 1]
        );
    }
}
