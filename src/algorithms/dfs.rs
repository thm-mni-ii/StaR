use crate::data_structures::graph::Graph;

//https://drops.dagstuhl.de/opus/volltexte/2015/4921/pdf/21.pdf

pub struct DFS<'a> {
    graph: &'a Graph,
    stack: Vec<(usize, u32)>,
    t: Vec<(usize, u32)>,
    colors: Vec<u8>,
    preprocess: bool,
}

impl<'a> Iterator for DFS<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.stack.is_empty() {
            for i in 0..self.colors.len() {
                if self.colors[i] == 0 && self.t.is_empty() {
                    self.push_to_stack((i, 0));
                    if self.preprocess {
                        return Some(i);
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
    pub fn new_preprocess(graph: &'a Graph) -> Self {
        Self {
            graph,
            stack: Vec::with_capacity(2),
            t: Vec::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: true,
        }
    }

    pub fn new_postprocess(graph: &'a Graph) -> Self {
        Self {
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
        let graph = Graph::new( 
            vec![0, 0, 0, 0, 0, 0],
            vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        );

        assert_eq!(DFS::new_preprocess(&graph).next().unwrap(), 0)
    }

    #[test]
    fn test_first_postprocess() {
        let graph = Graph::new( 
            vec![0, 0, 0, 0, 0, 0],
            vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        );

        assert_eq!(DFS::new_postprocess(&graph).next().unwrap(), 3);
    }

    #[test]
    fn test_whole_preprocess() {
        let graph = Graph::new( 
            vec![0, 0, 0, 0, 0, 0],
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
            DFS::new_preprocess(&graph).collect::<Vec<usize>>(),
            vec![0, 3, 2, 1, 4, 5]
        )
    }

    #[test]
    fn test_whole_postprocess() {
        let graph = Graph::new( 
            vec![0, 0, 0, 0, 0, 0],
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
            DFS::new_postprocess(&graph).collect::<Vec<usize>>(),
            vec![3, 4, 1, 2, 0, 5]
        )
    }
}
