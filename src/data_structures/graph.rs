use core::panic;
use std::io::{BufRead, BufReader, ErrorKind, Read};

type NodeType = usize;

#[derive(Debug, PartialEq)]
/// A basic graph data structure consisting of a vector of nodes and a vector of edges.
pub struct Graph {
    pub nodes: Vec<u8>, //0: valid entry, 1: invalid entry (deleted)
    pub edges: Vec<Vec<usize>>,
    pub back_edges: Vec<Vec<usize>>,
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
            nodes: Vec::new(),
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
            nodes: vec![0_u8; n],
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
            nodes: vec![0_u8; n],
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
        if index >= self.nodes.len() {
            panic!("node {} does not exist", index);
        }
        if self.nodes[index] == 1 {
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
    pub fn add_node(&mut self, edges: Vec<NodeType>) -> NodeType {
        self.nodes.push(0);
        self.edges.push(vec![]);
        self.back_edges.push(vec![]);

        edges.iter().for_each(|e| {
            if *e >= self.nodes.len() {
                panic!("edge {:?} contains non existent nodes", e);
            }
            if self.nodes[*e] == 1 {
                panic!("edge {:?} contains invalid nodes", e);
            }
            self.edges[self.nodes.len() - 1].push(*e);
            self.edges[*e].push(self.nodes.len() - 1);
            self.back_edges[self.nodes.len() - 1].push(self.edges[*e].len() - 1);
            self.back_edges[*e].push(self.edges[self.nodes.len() - 1].len() - 1);
        });

        self.nodes.len() - 1
    }

    /// Removes the node with index n from the graph.
    ///
    /// Time complexity: O(1)
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
        if index < self.nodes.len() {
            self.nodes[index] = 1;
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
            panic!("Fehler");
        }

        self.back_edges[edge.1].remove(
            self.edges[edge.1]
                .iter()
                .enumerate()
                .find(|e| *e.1 == edge.0)
                .map(|e| e.0)
                .unwrap(),
        );
        self.back_edges[edge.0].remove(
            self.edges[edge.0]
                .iter()
                .enumerate()
                .find(|e| *e.1 == edge.1)
                .map(|e| e.0)
                .unwrap(),
        );
        self.edges[edge.0].retain(|e| edge.1 != *e);
        self.edges[edge.1].retain(|e| edge.0 != *e)
    }
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
        let mut graph: Option<Graph> = None;
        let mut order: Option<usize> = None;
        for line in reader.lines() {
            let line = line?;
            let elements: Vec<_> = line.split(' ').collect();
            match elements[0] {
                "c" => {
                    // who cares about comments..
                }
                "p" => {
                    order = Some(parse_order(&elements)?);
                    graph = Some(Graph::new_with_nodes(order.unwrap()));
                }
                _ => match graph.as_mut() {
                    Some(graph) => {
                        let u = parse_vertex(elements[1], order.unwrap())?;
                        let v = parse_vertex(elements[2], order.unwrap())?;
                        graph.add_edge((u, v));
                    }
                    None => {
                        return Err(std::io::Error::new(
                            ErrorKind::Other,
                            "Edges encountered before graph creation",
                        ));
                    }
                },
            };
        }
        match graph {
            Some(graph) => Ok(graph),
            None => Err(std::io::Error::new(
                ErrorKind::Other,
                "No graph created during parsing",
            )),
        }
    }
}

fn parse_vertex(v: &str, order: usize) -> Result<usize, std::io::Error> {
    match v.parse::<usize>() {
        Ok(u) => {
            if u == 0 || u > order {
                Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "Invalid vertex label",
                ))
            } else {
                Ok(u - 1)
            }
        }
        Err(_) => Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid vertex label",
        )),
    }
}

fn parse_order(elements: &[&str]) -> Result<usize, std::io::Error> {
    if elements.len() < 3 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid line received starting with p",
        ));
    }
    match elements[2].parse::<usize>() {
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
    fn test_graph_reader_successful() {
        let test = "p edge 6 4\ne 1 4\ne 1 3\ne 2 5\ne 2 3".as_bytes();

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
    fn test_graph_reader_node_zero() {
        let test = "p edge 6 4\ne 1 4\ne 1 3\ne 2 0\ne 2 3".as_bytes();

        let graph = Graph::try_from(BufReader::new(test));
        assert!(graph.is_err())
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
