use core::panic;

type NodeType = usize;

#[derive(Debug)]
pub struct Graph {
    pub nodes: Vec<u8>, //0: valid entry, 1: invalid entry
    pub edges: Vec<Vec<usize>>,
}

impl Default for Graph {
    fn default() -> Self {
        Self::new()
    }
}

impl Graph {
    pub fn new() -> Self {
        Graph {
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }

    pub fn new_with_nodes(n: usize) -> Self {
        Graph {
            nodes: vec![0_u8; n],
            edges: vec![Vec::new(); n],
        }
    }

    pub fn new_with_edges(n: usize, edges: Vec<Vec<NodeType>>) -> Self {
        if edges.len() != n {
            panic!("Length of edge matrix has to be the same as number of nodes");
        }

        for i in 0..edges.len() {
            for j in 0..edges[i].len() {
                if !edges[edges[i][j]].contains(&i) {
                    panic!(
                        "edge ({}, {}) does not have an edge ({}, {})",
                        i, edges[i][j], edges[i][j], i
                    );
                }
            }
        }

        Graph {
            nodes: vec![0_u8; n],
            edges,
        }
    }

    pub fn neighbors(&self, index: NodeType) -> &Vec<NodeType> {
        if index >= self.nodes.len() {
            panic!("node {} does not exist", index);
        }
        if self.nodes[index] == 1 {
            panic!("node {} has been deleted", index);
        }
        &self.edges[index]
    }

    pub fn add_node(&mut self, edges: Vec<NodeType>) -> NodeType {
        self.nodes.push(0);
        self.edges.push(vec![]);

        edges.iter().for_each(|e| {
            if *e >= self.nodes.len() {
                panic!("edge {:?} contains non existent nodes", e);
            }
            if self.nodes[*e] == 1 {
                panic!("edge {:?} contains invalid nodes", e);
            }
            self.edges[self.nodes.len() - 1].push(*e);
            self.edges[*e].push(self.nodes.len() - 1);
        });

        self.nodes.len() - 1
    }

    pub fn remove_node(&mut self, index: NodeType) {
        if index < self.nodes.len() {
            self.nodes[index] = 1;
        }
    }

    pub fn add_edge(&mut self, edge: (NodeType, NodeType)) {
        if self.edges[edge.0].contains(&edge.1) {
            panic!("edge {:?} already exists", edge);
        }
        if edge.0 >= self.nodes.len() {
            panic!("node {} does not exist", edge.0);
        }
        if edge.1 >= self.nodes.len() {
            panic!("node {} does not exist", edge.1);
        }
        if self.nodes[edge.1] == 1 {
            panic!("node {} is invalid", edge.1);
        }
        if self.nodes[edge.0] == 1 {
            panic!("node {} is invalid", edge.0);
        }
        self.edges[edge.0].push(edge.1);
        self.edges[edge.1].push(edge.0);
    }

    pub fn remove_edge(&mut self, edge: (NodeType, NodeType)) {
        if self.edges[edge.0].contains(&edge.1) {
            self.edges[edge.0].retain(|e| edge.1 != *e)
        }
        if self.edges[edge.1].contains(&edge.0) {
            self.edges[edge.1].retain(|e| edge.0 != *e)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::data_structures::graph::Graph;

    #[test]
    #[should_panic]
    fn test_new_with_invalid_eges() {
        let _ = Graph::new_with_edges(2, vec![vec![1], vec![]]);
    }

    #[test]
    fn test_neigbors_empty() {
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
        assert_eq!(*graph.neighbors(5), []);
    }

    #[test]
    fn test_neigbors_multiple() {
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
        assert_eq!(*graph.neighbors(0), [3, 2]);
    }

    #[test]
    fn test_neigbors_one() {
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
        assert_eq!(*graph.neighbors(1), [4, 2]);
    }

    #[test]
    #[should_panic]
    fn test_neighbor_of_non_existing_node() {
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
        graph.neighbors(6);
    }

    #[test]
    #[should_panic]
    fn test_neighbor_of_invalid_node() {
        let mut graph = Graph::new_with_edges(
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
        graph.remove_node(2);
        graph.neighbors(2);
    }

    #[test]
    fn test_node_add() {
        let mut graph = Graph::new_with_edges(
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

        graph.add_node(vec![1, 2]);
        assert_eq!(graph.nodes, [0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(
            graph.edges,
            [
                [3, 2].to_vec(),
                [4, 2, 6].to_vec(),
                [0, 1, 6].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
                [1, 2].to_vec()
            ]
        )
    }

    #[test]
    #[should_panic]
    fn test_node_add_invalid_edge() {
        let mut graph = Graph::new_with_edges(
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
        graph.remove_node(2);
        graph.add_node(vec![2]);
    }

    #[test]
    #[should_panic]
    fn test_node_add_edge_to_non_existent_node() {
        let mut graph = Graph::new_with_edges(
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
        graph.add_node(vec![8]);
    }

    #[test]
    fn test_edge_add() {
        let mut graph = Graph::new_with_edges(
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
        graph.add_edge((3, 5));
        assert_eq!(
            graph.edges,
            vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0, 5].to_vec(),
                [1].to_vec(),
                [3].to_vec()
            ],
        );
    }

    #[test]
    #[should_panic]
    fn test_edge_add_invalid_node() {
        let mut graph = Graph::new_with_edges(
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
        graph.remove_node(2);
        graph.add_edge((3, 2));
    }

    #[test]
    #[should_panic]
    fn test_edge_add_non_existing_node() {
        let mut graph = Graph::new_with_edges(
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
        graph.add_edge((3, 7));
    }

    #[test]
    #[should_panic]
    fn test_edge_add_existing_edge() {
        let mut graph = Graph::new_with_edges(
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
        graph.add_edge((0, 3));
    }

    #[test]
    fn test_remove_node() {
        let mut graph = Graph::new_with_edges(
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
        graph.remove_node(3);
        assert_eq!(graph.nodes, [0, 0, 0, 1, 0, 0])
    }

    #[test]
    fn test_remove_edge() {
        let mut graph = Graph::new_with_edges(
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
        graph.remove_edge((0, 3));
        assert_eq!(
            graph.edges,
            vec![
                [2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [].to_vec(),
                [1].to_vec(),
                [].to_vec()
            ]
        );
    }
}
