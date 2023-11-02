use core::panic;
use std::io::{BufRead, BufReader, Error, ErrorKind, Read};

use super::bitvec::FastBitvec;

type NodeType = usize;

#[derive(Debug, PartialEq, Clone, Eq)]
/// A basic graph data structure consisting of a vector of nodes and a vector of edges.
pub struct Graph {
    pub deleted: FastBitvec, //O(n) bits
    //pub edges_deleted: Vec<FastBitvec>,
    pub nodes: usize, //0: valid entry, 1: invalid entry (deleted) O(1) Bits
    pub edges: Vec<Vec<usize>>, // O(n * (n - 1)) = O(n^2) Bits
    pub back_edges: Vec<Vec<usize>>, // O(n * (n - 1)) = O(n^2) Bits
}

impl Default for Graph {
    fn default() -> Self {
        Self::new()
    }
}

impl Graph {
    /// Returns empty graph without any nodes or edges.
    /// # Example
    /// ```
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new();
    /// ```
    pub fn new() -> Self {
        Graph {
            deleted: FastBitvec::new(0),
            nodes: 0,
            edges: Vec::new(),
            back_edges: Vec::new(),
        }
    }

    /// Returns graph with n nodes without any edges.
    /// # Example
    /// ```
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new_with_nodes(10);
    /// ```
    pub fn new_with_nodes(n: usize) -> Self {
        Graph {
            deleted: FastBitvec::new(n),
            nodes: n,
            edges: vec![Vec::new(); n],
            back_edges: vec![Vec::new(); n],
        }
    }

    /// Returns graph with n nodes and the given edges.
    /// # Example
    /// ```
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [1].to_vec(),
    ///         [0].to_vec(),
    ///     ],
    /// );
    /// ```
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

        let mut back_edges: Vec<Vec<usize>> = vec![Vec::new(); n];
        for i in 0..edges.len() {
            back_edges[i] = vec![0; edges[i].len()];
            for j in 0..edges[i].len() {
                let node = edges[i][j];
                back_edges[i][j] = edges[node]
                    .iter()
                    .enumerate()
                    .find(|n| *n.1 == i)
                    .map(|n| n.0)
                    .unwrap()
            }
        }

        Graph {
            deleted: FastBitvec::new(n),
            nodes: n,
            edges,
            back_edges,
        }
    }

    /// Returns neighboring nodes of the given node.
    ///
    /// Time complexity: O(1)
    /// # Example
    /// ```
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [1].to_vec(),
    ///         [0].to_vec(),
    ///     ],
    /// );
    ///
    /// assert_eq!(*graph.neighbors(0), vec![1])
    /// ```
    pub fn neighbors(&self, index: NodeType) -> &Vec<NodeType> {
        if index >= self.nodes {
            panic!("node {} does not exist", index);
        }
        if self.deleted.get(index) {
            panic!("node {} has been deleted", index);
        }
        &self.edges[index]
    }

    /// Adds a node to the graph, takes a Vec containing edges to that node. Returns the index of the new node.
    ///
    /// Time complexity: O(n)
    /// # Example
    /// ```
    /// use star::data_structures::graph::Graph;
    /// let mut graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [1].to_vec(),
    ///         [0].to_vec(),
    ///     ],
    /// );
    ///
    /// assert_eq!(graph.add_node(vec![0, 1]), 2)
    /// ```
    ///
    pub fn add_node(&mut self, edges: Vec<NodeType>) -> NodeType {
        self.nodes += 1;
        self.edges.push(vec![]);
        self.back_edges.push(vec![]);
        self.deleted.bitvec.push(false);

        edges.iter().for_each(|e| {
            if *e >= self.nodes {
                panic!("edge {:?} contains non existent nodes", e);
            }
            if self.deleted.get(*e) {
                panic!("edge {:?} contains invalid nodes", e);
            }
            self.edges[self.nodes - 1].push(*e);
            self.edges[*e].push(self.nodes - 1);
            self.back_edges[self.nodes - 1].push(self.edges[*e].len() - 1);
            self.back_edges[*e].push(self.edges[self.nodes - 1].len() - 1);
        });

        self.nodes - 1
    }

    /// Removes the node with index n from the graph. Also removes all edges to that node.
    ///
    /// Time complexity: O(n)
    /// # Example
    /// ```
    /// use star::data_structures::graph::Graph;
    /// let mut graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [1].to_vec(),
    ///         [0].to_vec(),
    ///     ],
    /// );
    ///
    /// graph.remove_node(1);
    /// ```
    pub fn remove_node(&mut self, index: NodeType) {
        if index < self.nodes {
            let neighbors = self.neighbors(index).clone();
            for n in neighbors {
                self.remove_edge((n, index))
            }
            self.deleted.set(index, true);
        }
    }

    /// Adds an edge to the graph.
    ///
    /// Time complexity: O(n)
    /// # Example
    /// ```
    /// use star::data_structures::graph::Graph;
    /// let mut graph = Graph::new_with_edges(
    ///     3,
    ///     vec![
    ///         [1, 2].to_vec(),
    ///         [0].to_vec(),
    ///         [0].to_vec()
    ///     ],
    /// );
    ///
    /// graph.add_edge((2, 1));
    /// assert_eq!(*graph.neighbors(2), vec![0, 1])
    /// ```
    //TDOD: hier muss auch noch das deleted kram mit rein
    pub fn add_edge(&mut self, edge: (NodeType, NodeType)) {
        if self.edges[edge.0].contains(&edge.1) {
            return;
        }
        if edge.0 >= self.nodes {
            panic!("node {} does not exist", edge.0);
        }
        if edge.1 >= self.nodes {
            panic!("node {} does not exist", edge.1);
        }
        if self.deleted.get(edge.1) {
            panic!("node {} is invalid", edge.1);
        }
        if self.deleted.get(edge.0) {
            panic!("node {} is invalid", edge.0);
        }
        self.edges[edge.0].push(edge.1);
        self.edges[edge.1].push(edge.0);
        self.back_edges[edge.1].push(self.edges[edge.0].len() - 1);
        self.back_edges[edge.0].push(self.edges[edge.1].len() - 1);
    }

    /// Removes an edge from the graph.
    ///
    /// Time complexity: O(n)
    /// # Example
    /// ```
    /// use star::data_structures::graph::Graph;
    /// let mut graph = Graph::new_with_edges(
    ///     3,
    ///     vec![
    ///         [1, 2].to_vec(),
    ///         [0].to_vec(),
    ///         [0].to_vec()
    ///     ],
    /// );
    ///
    /// graph.remove_edge((2, 0));
    /// assert_eq!(*graph.neighbors(2), vec![])
    /// ```
    pub fn remove_edge(&mut self, edge: (NodeType, NodeType)) {
        if !self.edges[edge.0].contains(&edge.1) || !self.edges[edge.1].contains(&edge.0) {
            return;
        }

        let i = self.edges[edge.0]
            .iter()
            .enumerate()
            .find(|(i, _)| self.edges[edge.0][*i] == edge.1)
            .unwrap()
            .0;

        let j = self.edges[edge.1]
            .iter()
            .enumerate()
            .find(|(i, _)| self.edges[edge.1][*i] == edge.0)
            .unwrap()
            .0;

        let len_0 = self.edges[edge.0].len();
        let last_edge_0 = self.edges[edge.0][len_0 - 1];
        let edge_0_in_last = self.edges[last_edge_0]
            .iter()
            .enumerate()
            .find(|(i, _)| self.edges[last_edge_0][*i] == edge.0)
            .unwrap()
            .0;
        self.back_edges[last_edge_0][edge_0_in_last] = i;
        let len_1 = self.edges[edge.1].len();
        let last_edge_1 = self.edges[edge.1][len_1 - 1];
        let edge_1_in_last = self.edges[last_edge_1]
            .iter()
            .enumerate()
            .find(|(i, _)| self.edges[last_edge_1][*i] == edge.1)
            .unwrap()
            .0;
        self.back_edges[last_edge_1][edge_1_in_last] = j;

        self.edges[edge.0].swap_remove(i);
        self.back_edges[edge.0].swap_remove(i);
        self.edges[edge.1].swap_remove(j);
        self.back_edges[edge.1].swap_remove(j);
    }

    /*pub fn remove_edge_unchecked(&mut self, edge: (NodeType, NodeType)) {
        self.back_edges[edge.0].remove(
            self.edges[edge.0]
                .iter()
                .enumerate()
                .find(|e| *e.1 == edge.1)
                .map(|e| e.0)
                .unwrap(),
        );
        self.edges[edge.0].retain(|e| edge.1 != *e);
    }*/
}

impl<U: Read> TryFrom<BufReader<U>> for Graph {
    type Error = std::io::Error;

    /// Reads a graph from a [.gr](https://pacechallenge.org/2019/vc/vc_format/) file and returns a Result containing either the parsed graph or an error.
    ///
    /// # Example
    /// ```
    /// use std::io::BufReader;
    /// use star::data_structures::graph::Graph;
    ///
    /// let test = "p edge 6 4\ne 1 4\ne 1 3\ne 2 5\ne 2 3".as_bytes();
    /// Graph::try_from(BufReader::new(test));
    /// ```

    fn try_from(reader: BufReader<U>) -> Result<Self, Self::Error> {
        let mut lines = reader.lines();
        let first_line = lines
            .next()
            .unwrap_or(Err(Error::new(ErrorKind::Other, "Empty file found")))?;
        let order = match parse_order(first_line.as_str()) {
            Ok(order) => Some(order),
            Err(_) => {
                return Err(std::io::Error::new(
                    ErrorKind::Other,
                    "Invalid order of graph",
                ))
            }
        };

        let mut graph = Graph::new_with_nodes(order.unwrap());

        for line in lines.skip(1) {
            let line = line?;
            let elements: Vec<_> = line.split_whitespace().collect();
            let u = parse_vertex(elements[0], order.unwrap())?;
            let v = parse_vertex(elements[1], order.unwrap())?;
            graph.add_edge((u, v));
        }

        Ok(graph)
    }
}

fn parse_vertex(v: &str, order: usize) -> Result<usize, std::io::Error> {
    match v.parse::<usize>() {
        Ok(u) => {
            if u >= order {
                Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    format!("Invalid vertex label {}", u),
                ))
            } else {
                Ok(u)
            }
        }
        Err(_) => Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid vertex label 1",
        )),
    }
}

fn parse_order(element: &str) -> Result<usize, std::io::Error> {
    match element.parse::<usize>() {
        Ok(order) => Ok(order),
        Err(_) => Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid order of graph",
        )),
    }
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use crate::data_structures::graph::Graph;

    #[test]
    fn test_back_edges() {
        let graph =
            Graph::new_with_edges(3, vec![[1, 2].to_vec(), [0, 2].to_vec(), [0, 1].to_vec()]);
        assert_eq!(graph.back_edges[1], vec![0, 1]);
        assert_eq!(graph.back_edges[2], vec![1, 1]);
    }

    #[test]
    fn test_back_edges_2() {
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
        assert_eq!(graph.back_edges[0], vec![0, 0]);
        assert_eq!(graph.back_edges[1], vec![0, 1]);
        assert_eq!(graph.back_edges[2], vec![1, 1]);
        assert_eq!(graph.back_edges[3], vec![0]);
        assert_eq!(graph.back_edges[4], vec![0]);
        assert_eq!(graph.back_edges[5], vec![]);

        graph.add_edge((2, 4));

        assert_eq!(graph.back_edges[2], vec![1, 1, 1]);
        assert_eq!(graph.back_edges[4], vec![0, 2]);
    }

    #[test]
    fn test_graph_reader_successful() {
        let test = "p 6 4\n0 3\n0 2\n1 4\n1 2".as_bytes();

        let graph = Graph::try_from(BufReader::new(test));
        assert_eq!(
            graph.unwrap(),
            Graph::new_with_edges(
                6,
                vec![
                    [3, 2].to_vec(),
                    [4, 2].to_vec(),
                    [0, 1].to_vec(),
                    [0].to_vec(),
                    [1].to_vec(),
                    [].to_vec(),
                ],
            )
        )
    }

    #[test]
    fn test_graph_reader_node_too_big() {
        let test = "p edge 6 4\ne 1 4\ne 1 3\ne 2 7\ne 2 3".as_bytes();

        let graph = Graph::try_from(BufReader::new(test));
        assert!(graph.is_err())
    }

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
        assert_eq!(graph.nodes, 7);
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
        assert_eq!(graph.nodes, 6)
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
        assert_eq!(graph.edges[0], vec![2]);
        assert_eq!(graph.edges[3], vec![]);
    }
}
