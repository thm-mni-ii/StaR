use crate::algorithms::dfs::*;
use core::panic;

pub struct Graph<'b> {
    pub labels: Vec<&'b str>,
    pub nodes: Vec<u8>, //0: valid entry, 1: invalid entry
    pub edges: Vec<Vec<usize>>,
}

impl<'b> Graph<'b> {
    pub fn new(labels: Vec<&'b str>, nodes: Vec<u8>, edges: Vec<Vec<usize>>) -> Self {
        Graph {
            labels,
            nodes,
            edges,
        }
    }

    pub fn dfs_preprocess(&self) -> DFS {
        DFS {
            graph: self,
            stack: Vec::with_capacity(self.nodes.len()),
            t: Vec::new(),
            colors: vec![0_u8; self.nodes.len()],
            preprocess: true,
        }
    }

    pub fn dfs_postprocess(&self) -> DFS {
        DFS {
            graph: self,
            stack: Vec::with_capacity(self.nodes.len()),
            t: Vec::new(),
            colors: vec![0_u8; self.nodes.len()],
            preprocess: false,
        }
    }

    pub fn neighbors(&self, index: usize) -> &Vec<usize> {
        if index >= self.nodes.len() {
            panic!("node {} does not exist", index);
        }
        if self.nodes[index] == 1 {
            panic!("node {} has been deleted", index);
        }
        &self.edges[index]
    }

    pub fn add_node(&mut self, label: &'b str, edges: Vec<usize>) {
        self.labels.push(<&str>::clone(&label));
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
    }

    pub fn remove_node(&mut self, index: usize) {
        if index < self.nodes.len() {
            self.nodes[index] = 1;
        }
    }

    pub fn add_edge(&mut self, edge: (usize, usize)) {
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

    pub fn remove_edge(&mut self, edge: (usize, usize)) {
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

    //test neighbors

    #[test]
    fn test_neigbors_empty() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        assert_eq!(*graph.neighbors(5), []);
    }

    #[test]
    fn test_neigbors_multiple() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        assert_eq!(*graph.neighbors(0), [3, 2]);
    }

    #[test]
    fn test_neigbors_one() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        assert_eq!(*graph.neighbors(1), [4, 2]);
    }

    #[test]
    #[should_panic]
    fn test_neighbor_of_non_existing_node() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        graph.neighbors(6);
    }

    #[test]
    #[should_panic]
    fn test_neighbor_of_invalid_node() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        graph.remove_node(2);
        graph.neighbors(2);
    }

    // test add_node

    #[test]
    fn test_node_add() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };

        graph.add_node("6", vec![1, 2]);
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
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        graph.remove_node(2);
        graph.add_node("6", vec![2]);
    }

    #[test]
    #[should_panic]
    fn test_node_add_edge_to_non_existent_node() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        graph.add_node("6", vec![8]);
    }

    // test add_edge

    #[test]
    fn test_edge_add() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
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
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        graph.remove_node(2);
        graph.add_edge((3, 2));
    }

    #[test]
    #[should_panic]
    fn test_edge_add_non_existing_node() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        graph.add_edge((3, 7));
    }

    #[test]
    #[should_panic]
    fn test_edge_add_existing_edge() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        graph.add_edge((0, 3));
    }

    // test remove_node

    #[test]
    fn test_remove_node() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
        graph.remove_node(3);
        assert_eq!(graph.nodes, [0, 0, 0, 1, 0, 0])
    }

    // test remove_edge

    #[test]
    fn test_remove_edge() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![
                [3, 2].to_vec(),
                [4, 2].to_vec(),
                [0, 1].to_vec(),
                [0].to_vec(),
                [1].to_vec(),
                [].to_vec(),
            ],
        };
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
