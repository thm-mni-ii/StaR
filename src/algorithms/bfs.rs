use crate::data_structures::graph::Graph;
use std::collections::VecDeque;

struct BFS<'a> {
    start: usize,
    start_needed: bool,
    graph: &'a Graph,
    colors: Vec<u8>,
    queue: VecDeque<(usize, u32)>,
    preprocess: bool,
}

impl<'a> Iterator for BFS<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start_needed {
            self.start_needed = false;
            self.queue.push_back((self.start, 0));

            if self.preprocess {
                return Some(self.start);
            }
        }

        if self.queue.is_empty() {
            for i in 0..self.colors.len() {
                if self.colors[i] == 0 {
                    self.queue.push_back((i, 0));
                    if self.preprocess {
                        return Some(i);
                    }
                    break;
                }
            }
            if self.queue.is_empty() {
                return None;
            }
        }
        let temp = self.queue.pop_front().unwrap();
        self.colors[temp.0] = 1; // gray
        let neighbors = self.graph.neighbors(temp.0);

        if temp.1 < (neighbors.len() as u32) {
            self.queue.push_back((temp.0, temp.1 + 1));

            if self.colors[neighbors[temp.1 as usize]] == 0 {
                self.queue.push_back((neighbors[temp.1 as usize], 0));
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

impl<'a> BFS<'a> {
    pub fn new_preprocess(graph: &'a Graph, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            graph,
            queue: VecDeque::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: true,
        }
    }

    pub fn new_postprocess(graph: &'a Graph, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            graph,
            queue: VecDeque::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{algorithms::bfs::BFS, data_structures::graph::Graph};

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
            BFS::new_preprocess(&graph, 0).collect::<Vec<usize>>(),
            [0, 3, 2, 1, 4, 5]
        );
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
            BFS::new_postprocess(&graph, 0).collect::<Vec<usize>>(),
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
            BFS::new_preprocess(&graph, 2).collect::<Vec<usize>>(),
            [2, 0, 1, 3, 4, 5]
        );
    }

    #[test]
    fn test_whole_postprocess_other_start() {
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
            BFS::new_postprocess(&graph, 2).collect::<Vec<usize>>(),
            [2, 0, 3, 1, 4, 5]
        );
    }
}