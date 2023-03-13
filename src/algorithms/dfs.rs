use crate::data_structures::graph::Graph;

//https://drops.dagstuhl.de/opus/volltexte/2015/4921/pdf/21.pdf

pub struct DFSSpaceEfficient<'a> {
    start: usize,
    start_needed: bool,
    graph: &'a Graph,
    stack: Vec<(usize, u32)>,
    t: Vec<usize>,
    colors: Vec<u8>,
    preprocess: bool,
}

impl<'a> Iterator for DFSSpaceEfficient<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start_needed {
            self.start_needed = false;
            self.push_to_stack((self.start, 0));

            if self.preprocess {
                return Some(self.start);
            }
        }

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

impl<'a> DFSSpaceEfficient<'a> {
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
            self.t.push(to_push.0);
        }
    }

    fn pop_from_stack(&mut self) -> (usize, u32) {
        if self.stack.is_empty() && !self.t.is_empty() {
            self.restore_segment();
        }
        if self.stack.len() == self.stack.capacity()
            || self.stack.len() == self.stack.capacity() / 2
        {
            self.t.pop();
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

        while self.stack.is_empty() || self.stack[self.stack.len() - 1].0 != old_top_of_t {
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

//-----------------------------------------------------------------------------------------------------------

enum NodeSize {
    Big(usize),
    Small(usize),
}

pub struct DFSLinearTime<'a> {
    start: usize,
    start_needed: bool,
    graph: &'a Graph,
    stack: Vec<(usize, usize)>,
    t: Vec<(usize, NodeSize)>,
    colors: Vec<u8>,
    preprocess: bool,
    d: Vec<Option<usize>>,
}

impl Iterator for DFSLinearTime<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start_needed {
            self.start_needed = false;
            self.push_to_stack((self.start, 0));

            if self.preprocess {
                return Some(self.start);
            }
        }

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

        if temp.1 < neighbors.len() {
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

impl<'a> DFSLinearTime<'a> {
    pub fn new_preprocess(graph: &'a Graph, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            graph,
            stack: Vec::with_capacity(2),
            t: Vec::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: true,
            d: vec![None; graph.nodes.len()],
        }
    }

    pub fn new_postprocess(graph: &'a Graph, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            graph,
            stack: Vec::with_capacity(2), //s'
            t: Vec::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: false,
            d: vec![None; graph.nodes.len()],
        }
    }

    fn push_to_stack(&mut self, to_push: (usize, usize)) {
        if self.stack.len() >= self.stack.capacity() {
            self.stack = Vec::with_capacity(self.stack.capacity());
        }
        self.stack.push((to_push.0, to_push.1));
        self.d[to_push.0] = Some(self.t.len());

        if self.stack.len() == self.stack.capacity()
            || self.stack.len() == self.stack.capacity() / 2
        {
            if self.graph.neighbors(to_push.0).len() < self.graph.get_edges().len() / 2 {
                self.t.push((to_push.0 /*Nummer der Gruppe*/,))
            } else {
                self.t.push((to_push.0, NodeSize::Big(to_push.1)))
            }
        }
    }

    fn pop_from_stack(&mut self) -> (usize, usize) {
        if self.stack.is_empty() {
            self.restore_segment();
        }
        if self.stack.len() == self.stack.capacity()
            || self.stack.len() == self.stack.capacity() / 2
        {
            self.t.pop();
        }
        self.stack.pop().unwrap()
    }

    fn restore_segment(&mut self) {
        self.start_needed = true;
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

            if temp.1 < neighbors.len() {
                self.push_to_stack((temp.0, temp.1 + 1));
                if self.d[neighbors[temp.1 as usize]].is_some()
                    && self.d[neighbors[temp.1 as usize]].unwrap() == self.t.len()
                    && self.colors[neighbors[temp.1 as usize]] == 1
                {
                    self.push_to_stack((neighbors[temp.1 as usize], 0));
                    self.colors[neighbors[temp.1 as usize]] = 0;
                }
            } else {
                self.colors[temp.0] = 2;
            }

            for i in 0..self.stack.len() {
                self.colors[self.stack[i].0] = 1;
            }
        }
    }
}

//-----------------------------------------------------------------------------------------------------------

pub struct StandardDFS<'a> {
    start: usize,
    start_needed: bool,
    graph: &'a Graph,
    stack: Vec<(usize, u32)>,
    colors: Vec<u8>,
    preprocess: bool,
}

impl Iterator for StandardDFS<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start_needed {
            self.start_needed = false;
            self.stack.push((self.start, 0));

            if self.preprocess {
                return Some(self.start);
            }
        }

        if self.stack.is_empty() {
            for i in 0..self.colors.len() {
                if self.colors[i] == 0 {
                    self.stack.push((i, 0));
                    if self.preprocess {
                        return Some(i);
                    }
                    break;
                }
            }
            if self.stack.is_empty() {
                return None;
            }
        }

        let temp = self.stack.pop().unwrap();
        self.colors[temp.0] = 1; // gray
        let neighbors = self.graph.neighbors(temp.0);

        if temp.1 < (neighbors.len() as u32) {
            self.stack.push((temp.0, temp.1 + 1));

            if self.colors[neighbors[temp.1 as usize]] == 0 {
                self.stack.push((neighbors[temp.1 as usize], 0));
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

impl<'a> StandardDFS<'a> {
    pub fn new_preprocess(graph: &'a Graph, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            graph,
            stack: Vec::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: true,
        }
    }

    pub fn new_postprocess(graph: &'a Graph, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            graph,
            stack: Vec::new(),
            colors: vec![0_u8; graph.nodes.len()],
            preprocess: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        algorithms::dfs::{DFSLinearTime, DFSSpaceEfficient, StandardDFS},
        data_structures::graph::Graph,
    };

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

        assert_eq!(
            DFSSpaceEfficient::new_preprocess(&graph, 0).next().unwrap(),
            0
        );
        assert_eq!(StandardDFS::new_preprocess(&graph, 0).next().unwrap(), 0);
        assert_eq!(DFSLinearTime::new_preprocess(&graph, 0).next().unwrap(), 0);
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

        assert_eq!(
            DFSSpaceEfficient::new_postprocess(&graph, 0)
                .next()
                .unwrap(),
            3
        );
        assert_eq!(StandardDFS::new_postprocess(&graph, 0).next().unwrap(), 3);
        assert_eq!(DFSLinearTime::new_postprocess(&graph, 0).next().unwrap(), 3);
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
            DFSSpaceEfficient::new_preprocess(&graph, 0).collect::<Vec<usize>>(),
            vec![0, 3, 2, 1, 4, 5]
        );
        assert_eq!(
            StandardDFS::new_preprocess(&graph, 0).collect::<Vec<usize>>(),
            vec![0, 3, 2, 1, 4, 5]
        );
        /*assert_eq!(
            DFSLinearTime::new_preprocess(&graph, 0).collect::<Vec<usize>>(),
            vec![0, 3, 2, 1, 4, 5]
        )*/
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
            DFSSpaceEfficient::new_postprocess(&graph, 0).collect::<Vec<usize>>(),
            vec![3, 4, 1, 2, 0, 5]
        );
        assert_eq!(
            StandardDFS::new_postprocess(&graph, 0).collect::<Vec<usize>>(),
            vec![3, 4, 1, 2, 0, 5]
        );
        assert_eq!(
            DFSLinearTime::new_postprocess(&graph, 0).collect::<Vec<usize>>(),
            vec![3, 4, 1, 2, 0, 5]
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
            DFSSpaceEfficient::new_preprocess(&graph, 2).collect::<Vec<usize>>(),
            vec![2, 0, 3, 1, 4, 5]
        );
        assert_eq!(
            StandardDFS::new_preprocess(&graph, 2).collect::<Vec<usize>>(),
            vec![2, 0, 3, 1, 4, 5]
        );
        assert_eq!(
            DFSLinearTime::new_preprocess(&graph, 2).collect::<Vec<usize>>(),
            vec![2, 0, 3, 1, 4, 5]
        );
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
            DFSSpaceEfficient::new_postprocess(&graph, 2).collect::<Vec<usize>>(),
            vec![3, 0, 4, 1, 2, 5]
        );
        assert_eq!(
            StandardDFS::new_postprocess(&graph, 2).collect::<Vec<usize>>(),
            vec![3, 0, 4, 1, 2, 5]
        );
        assert_eq!(
            DFSLinearTime::new_postprocess(&graph, 2).collect::<Vec<usize>>(),
            vec![3, 0, 4, 1, 2, 5]
        );
    }
}
