use crate::data_structures::graph::Graph;

use super::bfs::GraphLike;

/// An iterator iterating over nodes of a graph in depth-first-search order as described in https://drops.dagstuhl.de/opus/volltexte/2015/4921/pdf/21.pdf.
pub struct DFS<'a> {
    start: usize,
    start_needed: bool,
    graph: &'a Graph,
    stack: Vec<(usize, u32)>,
    t: Vec<(usize, u32)>,
    colors: Vec<u8>,
    preprocess: bool,
}

impl<'a> Iterator for DFS<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start_needed {
            self.start_needed = false;
            self.push_to_stack((self.start, 0));

            if self.preprocess {
                return Some(self.start);
            }
        }

        if self.stack.is_empty() && self.t.is_empty() {
            return None;
        }

        let temp = self.pop_from_stack();
        self.colors[temp.0] = 1; // gray
        let neighbors = self.graph.neighbors(temp.0);

        if temp.1 < (neighbors.len() as u32) {
            self.push_to_stack((temp.0, temp.1 + 1));

            if self.colors[neighbors[temp.1 as usize]] == 0 {
                self.push_to_stack((neighbors[temp.1 as usize], 0));
                if self.preprocess {
                    return Some(neighbors[temp.1 as usize]);
                }
            }
        } else {
            self.colors[temp.0] = 2;
            if !self.preprocess {
                return Some(temp.0);
            }
        }
        self.next()
    }
}

impl<'a> DFS<'a> {
    /// Returns a DFS iterator iterating over nodes of the given graph in preprocess order. Takes a reference to a graph and a starting node as arguments.
    ///
    /// Time complexity for entire DFS: O((n + m) log n)
    /// # Example
    /// ```
    /// use star::algorithms::dfs::DFS;
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [1].to_vec(),
    ///         [0].to_vec(),
    ///     ],
    /// );
    ///
    ///  DFS::new_preprocess(&graph, 0);
    /// ```

    pub fn new_preprocess(graph: &'a Graph, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            graph,
            stack: Vec::with_capacity(2),
            t: Vec::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: true,
        }
    }

    /// Returns a DFS iterator iterating over nodes of the given graph in postprocess order. Takes a reference to a graph and a starting node as arguments.
    ///
    /// Time complexity per `next()` call: O((n + m) log n)
    /// # Example
    /// ```
    /// use star::algorithms::dfs::DFS;
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///     ],
    /// );
    ///
    ///  DFS::new_postprocess(&graph, 0);
    /// ```

    pub fn new_postprocess(graph: &'a Graph, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            graph,
            stack: Vec::with_capacity(2),
            t: Vec::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: false,
        }
    }

    fn push_to_stack(&mut self, to_push: (usize, u32)) {
        if self.stack.len() >= self.stack.capacity() {
            self.stack = Vec::with_capacity(self.stack.capacity());
        }
        self.stack.push(to_push);

        if self.stack.len() == self.stack.capacity()
            || self.stack.len() == self.stack.capacity() / 2
        {
            self.t.push(to_push);
        }
    }

    fn pop_from_stack(&mut self) -> (usize, u32) {
        if self.stack.is_empty() && !self.t.is_empty() {
            self.restore_segment();
        }
        if self.stack.len() == self.stack.capacity()
            || self.stack.len() == self.stack.capacity() / 2
        {
            self.t.pop().unwrap();
        }
        self.stack.pop().unwrap()
    }

    fn restore_segment(&mut self) {
        self.start_needed = true;
        for c in 0..self.colors.len() {
            if self.colors[c] == (1_u8) {
                self.colors[c] = 0;
            }
        }
        let old_top_of_t = self.t[self.t.len() - 1];
        self.t = Vec::new();

        while self.stack.is_empty() || self.stack[self.stack.len() - 1].0 != old_top_of_t.0 {
            if self.start_needed {
                self.start_needed = false;
                self.push_to_stack((self.start, 0));
            }

            if self.stack.is_empty() {
                for i in 0..self.colors.len() {
                    if self.colors[i] == 0 {
                        self.push_to_stack((i, 0));
                        break;
                    }
                }
            }
            let temp = self.pop_from_stack();
            self.colors[temp.0] = 1; // gray
            let neighbors = self.graph.neighbors(temp.0);

            if temp.1 < (neighbors.len() as u32) {
                self.push_to_stack((temp.0, temp.1 + 1));
                if self.colors[neighbors[temp.1 as usize]] == 0 {
                    self.push_to_stack((neighbors[temp.1 as usize], 0));
                }
            } else {
                self.colors[temp.0] = 2;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{algorithms::dfs::DFS, data_structures::graph::Graph};

    #[test]
    fn test_first_preprocess() {
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

        assert_eq!(DFS::new_preprocess(&graph, 0).next().unwrap(), 0)
    }

    #[test]
    fn test_first_postprocess() {
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

        assert_eq!(DFS::new_postprocess(&graph, 0).next().unwrap(), 3);
    }

    #[test]
    fn test_whole_preprocess() {
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
            DFS::new_preprocess(&graph, 0).collect::<Vec<usize>>(),
            vec![0, 3, 2, 1, 4]
        )
    }

    #[test]
    fn test_whole_postprocess() {
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
            DFS::new_postprocess(&graph, 0).collect::<Vec<usize>>(),
            vec![3, 4, 1, 2, 0]
        )
    }

    #[test]
    fn test_other_start_preprocess() {
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
            DFS::new_preprocess(&graph, 2).collect::<Vec<usize>>(),
            vec![2, 0, 3, 1, 4]
        )
    }

    #[test]
    fn test_other_start_postprocess() {
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
            DFS::new_postprocess(&graph, 2).collect::<Vec<usize>>(),
            vec![3, 0, 4, 1, 2]
        )
    }
}
