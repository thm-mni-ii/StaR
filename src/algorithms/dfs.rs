use crate::data_structures::graph::Graph;

pub struct DFS<'a> {
    pub graph: &'a Graph<'a>,
    pub stack: Vec<(usize, u32)>,
    pub t: Vec<(usize, u32)>,
    pub colors: Vec<u8>,
    pub preprocess: bool,
}

impl<'a> Iterator for DFS<'a> {
    type Item = (&'a str, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            for i in 0..self.colors.len() {
                if self.colors[i] == 0 && self.t.is_empty() {
                    self.push_to_stack((i, 0));
                    if self.preprocess {
                        return Some((self.graph.labels[i], i));
                    }
                    break;
                }
            }
            if self.stack.is_empty() && self.t.is_empty() {
                return None;
            }
        }

        let temp = self.pop_from_stack();
        self.colors[temp.0] = 1; // gray
        let neighbors = self.graph.neighbors(temp.0);

        if temp.1 < (neighbors.len() as u32) {
            self.push_to_stack((temp.0, temp.1 + 1));

            if self.colors[neighbors[temp.1 as usize]] == 0 {
                self.push_to_stack((neighbors[temp.1 as usize], 0));
                if self.preprocess {
                    return Some((
                        self.graph.labels[neighbors[temp.1 as usize]],
                        neighbors[temp.1 as usize],
                    ));
                }
            }
        } else {
            self.colors[temp.0] = 2;
            if !self.preprocess {
                return Some((self.graph.labels[temp.0], temp.0));
            }
        }
        self.next()
    }
}

impl DFS<'_> {
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
        println!("restoring..");
        for c in 0..self.colors.len() {
            if self.colors[c] == (1_u8) {
                self.colors[c] = 0;
            }
        }
        let old_top_of_t = self.t[self.t.len() - 1];
        self.t = Vec::new();

        while self.stack.is_empty() || self.stack[self.stack.len() - 1].0 != old_top_of_t.0 {
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
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        assert_eq!(graph.dfs_preprocess().next().unwrap().1, 0)
    }

    #[test]
    fn test_first_postprocess() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        assert_eq!(graph.dfs_postprocess().next().unwrap().1, 3);
    }

    #[test]
    fn test_whole_preprocess() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        assert_eq!(
            graph.dfs_preprocess().map(|e| e.1).collect::<Vec<usize>>(),
            vec![0, 3, 2, 1, 4, 5]
        )
    }

    #[test]
    fn test_whole_postprocess() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        assert_eq!(
            graph.dfs_postprocess().map(|e| e.1).collect::<Vec<usize>>(),
            vec![3, 4, 1, 2, 0, 5]
        )
    }

    #[test]
    fn test_whole_preprocess_with_overflow() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        let preprocess = DFS {
            graph: &graph,
            stack: Vec::with_capacity(graph.nodes.len()),
            t: Vec::new(),
            colors: vec![0 as u8; graph.nodes.len()],
            preprocess: true,
        };

        assert_eq!(
            preprocess.map(|e| e.1).collect::<Vec<usize>>(),
            vec![0, 3, 2, 1, 4, 5]
        )
    }

    #[test]
    fn test_whole_postprocess_with_overflow() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        let postprocess = DFS {
            graph: &graph,
            stack: Vec::with_capacity(graph.nodes.len()),
            t: Vec::new(),
            colors: vec![0 as u8; graph.nodes.len()],
            preprocess: false,
        };

        assert_eq!(
            postprocess.map(|e| e.1).collect::<Vec<usize>>(),
            vec![3, 4, 1, 2, 0, 5]
        )
    }

    #[test]
    fn test_first_preprocess_with_overflow() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        let mut preprocess = DFS {
            graph: &graph,
            stack: Vec::with_capacity(graph.nodes.len()),
            t: Vec::new(),
            colors: vec![0 as u8; graph.nodes.len()],
            preprocess: true,
        };

        assert_eq!(preprocess.next().unwrap().1, 0);
    }

    #[test]
    fn test_first_postprocess_with_overflow() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        let mut postprocess = DFS {
            graph: &graph,
            stack: Vec::with_capacity(graph.nodes.len()),
            t: Vec::new(),
            colors: vec![0 as u8; graph.nodes.len()],
            preprocess: false,
        };

        assert_eq!(postprocess.next().unwrap().1, 3);
    }
}
