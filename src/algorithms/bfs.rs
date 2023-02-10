use crate::data_structures::graph::Graph;
use std::collections::VecDeque;

/// An iterator iterating over nodes of a graph in a bredth-first-search order
pub struct BFS<'a> {
    start: Option<usize>,
    graph: &'a Graph,
    visited: Vec<bool>,
    queue: VecDeque<usize>,
}

impl<'a> Iterator for BFS<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start.is_some() {
            self.queue.push_back(self.start.unwrap());
            self.start = None;
        }

        if self.queue.is_empty() {
            for i in 0..self.visited.len() {
                if !self.visited[i] {
                    self.queue.push_back(i);
                    break;
                }
            }
            if self.queue.is_empty() {
                return None;
            }
        }
        let temp = self.queue.pop_front().unwrap();
        self.visited[temp] = true;
        let neighbors = self.graph.neighbors(temp);

        for n in neighbors {
            if !self.visited[*n] {
                self.queue.push_back(*n);
            }
        }

        Some(temp)
    }
}

impl<'a> BFS<'a> {
    /// Returns a new BFS iterator. Takes a reference to a graph and a starting node.
    ///
    /// # Example
    /// ```
    /// use star::algorithms::bfs::BFS;
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///     ],
    /// );
    ///
    ///  BFS::new(&graph, 0);
    /// ```

    pub fn new(graph: &'a Graph, start: usize) -> Self {
        Self {
            start: Some(start),
            graph,
            queue: VecDeque::new(),
            visited: vec![false; graph.nodes.len()],
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{algorithms::bfs::BFS, data_structures::graph::Graph};

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
            BFS::new(&graph, 0).collect::<Vec<usize>>(),
            [0, 3, 2, 1, 4, 5]
        );
    }

    #[test]
    fn test_whole_preprocess_other_start() {
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
            BFS::new(&graph, 2).collect::<Vec<usize>>(),
            [2, 0, 1, 3, 4, 5]
        );
    }
}
