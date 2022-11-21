use core::panic;
use crate::algorithms::dfs::*;

pub struct Graph<'b> {
    pub labels: Vec<&'b str>,
    pub nodes: Vec<u8>, //0: valid entry, 1: invalid entry
    pub edges: Vec<(u32, u32)>,
}

impl<'b> Graph<'b> {
    pub fn new(labels: Vec<&'b str>, nodes: Vec<u8>, edges: Vec<(u32, u32)>) -> Self {
        Graph {
            labels: labels,
            nodes: nodes,
            edges: edges
        }
    }

    pub fn dfs_preprocess(&self) -> DFS {
        DFS {
            graph: self,
            stack: Vec::with_capacity(self.nodes.len()),
            t: Vec::new(),
            colors: vec![0 as u8; self.nodes.len()],
            preprocess: true,
        }
    }

    pub fn dfs_postprocess(&self) -> DFS {
        DFS {
            graph: self,
            stack: Vec::with_capacity(self.nodes.len()),
            t: Vec::new(),
            colors: vec![0 as u8; self.nodes.len()],
            preprocess: false,
        }
    }

    pub fn neighbors(&self, index: usize) -> Vec<usize> {
        if index >= self.nodes.len() {
            panic!("node {} does not exist", index);
        }
        if self.nodes[index] == 1 {
            panic!("node {} has been deleted", index);
        }
        let edges_containing_index: Vec<&(u32, u32)> = self.edges
            .iter()
            .filter(|e| e.0 as usize == index)
            .collect();
        let other_nodes: Vec<usize> = edges_containing_index
            .iter()
            .map(|e| e.1 as usize)
            .collect();

        other_nodes
    }

    pub fn add_node(&mut self, label: &'b str, edges: Vec<(u32, u32)>) {
        self.labels.push(&(*label.clone()));
        self.nodes.push(0);
        edges.iter()
            .for_each(|e| {
                if e.0 as usize >= self.nodes.len() || e.1 as usize >= self.nodes.len() {
                    panic!("edge {:?} contains non existent nodes", e);
                }
                if self.nodes[e.0 as usize] == 1 || self.nodes[e.1 as usize] == 1 {
                    panic!("edge {:?} contains invalid nodes", e);
                }
                self.edges.push(*e)
            }); 
    }

    pub fn remove_node(&mut self, index: usize) {
        if index < self.nodes.len() {
            self.nodes[index] = 1;
        }
    }

    pub fn add_edge(&mut self, e: (u32, u32)) {
        if self.edges.contains(&e) {
            panic!("edge {:?} already exists", e);
        }
        if e.0 as usize >= self.nodes.len() || e.1 as usize >= self.nodes.len() {
            panic!("edge {:?} contains non existent nodes", e);
        }
        if self.nodes[e.0 as usize] == 1 || self.nodes[e.1 as usize] == 1 {
            panic!("edge {:?} contains invalid nodes", e);
        }
        self.edges.push(e);
    }

    pub fn remove_edge(&mut self, edge: (u32, u32)) {
        if self.edges.contains(&edge) {
            self.edges = self.edges
                .iter()
                .filter(|e| edge.0 != e.0 || edge.1 != e.1)
                .map(|e| *e)
                .collect();
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
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        assert_eq!(graph.neighbors(5), []);
    }

    #[test]
    fn test_neigbors_multiple() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        assert_eq!(graph.neighbors(0), [3, 2]);
    }

    #[test]
    fn test_neigbors_one() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        assert_eq!(graph.neighbors(1), [4]);
    }

    #[test]
    #[should_panic]
    fn test_neighbor_of_non_existing_node() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        graph.neighbors(6);
    }

    #[test]
    #[should_panic]
    fn test_neighbor_of_invalid_node() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        graph.remove_node(2);
        graph.neighbors(2);
    }

    // test ass_node

    #[test]
    fn test_node_add() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        
        graph.add_node("6", vec![(6, 1), (6, 2)]);
        assert_eq!(graph.nodes, [0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    #[should_panic]
    fn test_node_add_invalid_edge() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        graph.remove_node(2);
        graph.add_node("6", vec![(6, 2)]);
    }

    #[test]
    #[should_panic]
    fn test_node_add_edge_to_non_existent_node() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        graph.add_node("6", vec![(6, 8)]);
    }

    // test add_edge

    #[test]
    fn test_edge_add() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        graph.add_edge((3, 5));
        assert_eq!(graph.edges, [(0, 3), (0, 2), (1, 4), (2, 1), (4, 1), (3, 5)]);
    }

    #[test]
    #[should_panic]
    fn test_edge_add_invalid_node() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
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
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        graph.add_edge((3, 7));
    }

    #[test]
    #[should_panic]
    fn test_edge_add_existing_edge() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        graph.add_edge((0, 3));
    }

    // test remove_node

    #[test]
    fn test_remove_node() {
        let mut graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
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
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        graph.remove_edge((0, 3));
        assert_eq!(graph.edges, [(0, 2), (1, 4), (2, 1), (4, 1)]);
    }
}
