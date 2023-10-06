use crate::algorithms::bfs::GraphLike;
use core::panic;

use super::{bitvec::FastBitvec, graph::Graph};

#[derive(Debug, PartialEq, Clone, Eq)]
/// Data structure representing Subgraphs
pub struct Subgraph<'a> {
    pub graph: &'a Graph,
    pub subset: FastBitvec,
    pub subset_edges: Vec<FastBitvec>,
}

impl GraphLike for Subgraph<'_> {
    /// returns the neighbors of a node in the subgraph. Panics if the node is not part of the subgraph
    ///
    /// # Example
    /// ```
    /// use star::data_structures::{choice_dict::ChoiceDict, graph::Graph};
    /// use star::data_structures::subgraph::Subgraph;
    /// let graph = Graph::new_with_edges(
    ///     6,
    ///     vec![
    ///         [3, 2].to_vec(),
    ///         [4, 2].to_vec(),
    ///         [0, 1].to_vec(),
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///         [].to_vec(),
    ///     ],
    /// );
    ///
    ///
    /// let mut subset = ChoiceDict::new(graph.nodes.len());
    /// let mut sub = Subgraph::new(&graph, subset);
    /// sub.add_to_subgraph(3);
    /// sub.neighbors(3);
    /// ```
    fn neighbors(&self, node: usize) -> Vec<usize> {
        if !self.subset.get(node) {
            panic!("node {} is not part of the subgraph", node);
        }

        self.graph
            .neighbors(node)
            .iter()
            .enumerate()
            .filter(|(i, n)| self.subset.get(**n) && self.subset_edges[node].get(*i))
            .map(|(_, n)| *n)
            .collect()
    }

    /// returns the nodes of the subgraph
    ///
    /// /// # Example
    /// ```
    /// use star::data_structures::{choice_dict::ChoiceDict, graph::Graph};
    /// use star::data_structures::subgraph::Subgraph;
    /// let graph = Graph::new_with_edges(
    ///     6,
    ///     vec![
    ///         [3, 2].to_vec(),
    ///         [4, 2].to_vec(),
    ///         [0, 1].to_vec(),
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///         [].to_vec(),
    ///     ],
    /// );
    ///
    ///
    /// let mut subset = ChoiceDict::new(graph.nodes.len());
    /// let mut sub = Subgraph::new(&graph, subset);
    /// sub.add_to_subgraph(3);
    /// sub.get_nodes();
    /// ```
    fn get_nodes(&self) -> Vec<usize> {
        self.subset.iter_1().collect()
    }
}

impl<'a> Subgraph<'a> {
    /// Returns a new Subgraph based on a Graph and a Choice Dictionary, that says what nodes belong to the Subgraph
    ///
    ///  # Example
    ///  ```
    /// use star::data_structures::{choice_dict::ChoiceDict, graph::Graph};
    /// use star::data_structures::subgraph::Subgraph;
    /// let graph = Graph::new_with_edges(
    ///     6,
    ///     vec![
    ///         [3, 2].to_vec(),
    ///         [4, 2].to_vec(),
    ///         [0, 1].to_vec(),
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///         [].to_vec(),
    ///     ],
    /// );
    ///
    ///
    /// let mut subset = ChoiceDict::new(graph.nodes.len());
    /// subset.set(0);
    /// subset.set(3);
    /// subset.set(4);
    ///
    /// let sub = Subgraph::new(&graph, subset);
    /// ```
    pub fn new(graph: &'a Graph, subset: Vec<usize>) -> Self {
        let mut subset_vec = FastBitvec::new(graph.nodes.len());
        subset.iter().for_each(|n| subset_vec.set(*n, true));
        let mut subset_edges = Vec::new();
        for i in 0..graph.nodes.len() {
            let neighbors = graph.neighbors(i);
            subset_edges.push(FastBitvec::new(neighbors.len()));
            if subset_vec.get(i) {
                neighbors.iter().enumerate().for_each(|(n, node)| {
                    if subset_vec.get(*node) {
                        subset_edges[i].set(n, true);
                    }
                });
            }
        }
        Subgraph {
            graph,
            subset: subset_vec,
            subset_edges,
        }
    }

    /// adds a node to the Subgraph. Panics if the node is not part of the original graph or has been deleted
    ///
    /// # Example
    /// ```
    /// use star::data_structures::{choice_dict::ChoiceDict, graph::Graph};
    /// use star::data_structures::subgraph::Subgraph;
    /// let graph = Graph::new_with_edges(
    ///     6,
    ///     vec![
    ///         [3, 2].to_vec(),
    ///         [4, 2].to_vec(),
    ///         [0, 1].to_vec(),
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///         [].to_vec(),
    ///     ],
    /// );
    ///
    ///
    /// let mut subset = ChoiceDict::new(graph.nodes.len());
    /// let mut sub = Subgraph::new(&graph, subset);
    /// sub.add_to_subgraph(3);
    /// ```
    pub fn add_to_subgraph(&mut self, node: usize) {
        if node >= self.graph.nodes.len() {
            panic!("node {} does not exist", node)
        }
        if self.graph.nodes[node] == 1 {
            panic!("node {} has been deleted", node)
        }

        self.subset.set(node, true);
        let neighbors = self.graph.neighbors(node);
        for i in neighbors.iter().enumerate() {
            if self.subset.get(neighbors[i.0]) {
                self.subset_edges[node].set(i.0, true);
                self.subset_edges[neighbors[i.0]].set(
                    self.graph
                        .neighbors(neighbors[i.0])
                        .iter()
                        .enumerate()
                        .find(|(_, n)| **n == node)
                        .map(|(i, _)| i)
                        .unwrap(),
                    true,
                );
            }
        }
    }

    /// removes a node from the subgraph. Panics if the node to remove doed not exist.
    ///
    /// # Example
    /// ```
    /// use star::data_structures::{choice_dict::ChoiceDict, graph::Graph};
    /// use star::data_structures::subgraph::Subgraph;
    /// let graph = Graph::new_with_edges(
    ///     6,
    ///     vec![
    ///         [3, 2].to_vec(),
    ///         [4, 2].to_vec(),
    ///         [0, 1].to_vec(),
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///         [].to_vec(),
    ///     ],
    /// );
    ///
    ///
    /// let mut subset = ChoiceDict::new(graph.nodes.len());
    /// let mut sub = Subgraph::new(&graph, subset);
    /// sub.add_to_subgraph(3);
    /// sub.remove_from_subgraph(3);
    /// ```
    pub fn remove_from_subgraph(&mut self, node: usize) {
        if node >= self.graph.nodes.len() {
            panic!("node {} does not exist", node)
        }

        self.subset.set(node, false);
        self.subset_edges[node] = FastBitvec::new(self.graph.neighbors(node).len());
    }

    pub fn remove_edge(&mut self, edge: (usize, usize)) {
        if !self.subset.get(edge.0) || !self.subset.get(edge.1) {
            return;
        }

        let a = self.graph.edges[edge.0]
            .iter()
            .enumerate()
            .find(|(_, n)| **n == edge.1)
            .map(|(i, _)| i);
        if a.is_none() {
            return;
        }
        let b = self.graph.edges[edge.1]
            .iter()
            .enumerate()
            .find(|(_, n)| **n == edge.0)
            .map(|(i, _)| i);

        if a.is_none() {
            return;
        }

        self.subset_edges[edge.0].set(a.unwrap(), false);
        self.subset_edges[edge.1].set(b.unwrap(), false);
    }

    pub fn add_edge(&mut self, edge: (usize, usize)) {
        if !self.subset.get(edge.0) || !self.subset.get(edge.1) {
            panic!("node {} or {} is not part of the subgraph", edge.0, edge.1)
        }

        let a = self.graph.edges[edge.0].iter().find(|n| **n == edge.1);
        if a.is_none() {
            return;
        }
        let b = self.graph.edges[edge.1].iter().find(|n| **n == edge.0);
        if a.is_none() {
            return;
        }

        self.subset_edges[edge.0].set(*a.unwrap(), true);
        self.subset_edges[edge.1].set(*b.unwrap(), true);
    }
}

#[cfg(test)]
mod tests {
    use crate::{algorithms::bfs::GraphLike, data_structures::graph::Graph};

    use super::Subgraph;

    #[test]
    fn test_new_subgraph() {
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

        let subset = vec![0, 3, 4];

        let sub = Subgraph::new(&graph, subset);

        assert_eq!(sub.graph, &graph);
        assert_eq!(sub.get_nodes(), vec![0, 3, 4])
    }

    #[test]
    fn test_add_to_subgraph() {
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

        let subset = vec![0, 3, 4];

        let mut sub = Subgraph::new(&graph, subset);

        sub.add_to_subgraph(1);

        assert_eq!(sub.get_nodes(), vec![0, 1, 3, 4])
    }

    #[test]
    fn test_remove_from_subgraph() {
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

        let subset = vec![0, 3, 4];

        let mut sub = Subgraph::new(&graph, subset);

        sub.remove_from_subgraph(3);

        assert_eq!(sub.get_nodes(), vec![0, 4])
    }

    #[test]
    fn test_neighbors() {
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

        let subset = vec![0, 3, 4];

        let sub = Subgraph::new(&graph, subset);

        assert_eq!(sub.neighbors(3), vec![0])
    }

    #[test]
    fn test_get_nodes() {
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

        let subset = vec![0, 3, 4];

        let sub = Subgraph::new(&graph, subset);

        assert_eq!(sub.get_nodes(), vec![0, 3, 4])
    }

    #[test]
    #[should_panic]
    fn test_neighbors_panic() {
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

        let subset = vec![0, 3, 4];

        let sub = Subgraph::new(&graph, subset);

        sub.neighbors(5);
    }

    #[test]
    #[should_panic]
    fn test_add_to_subgraph_panic() {
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

        let subset = vec![0, 3, 4];

        let mut sub = Subgraph::new(&graph, subset);

        sub.add_to_subgraph(6);
    }

    #[test]
    #[should_panic]
    fn test_add_to_subgraph_panic_deleted() {
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

        let subset = vec![0, 3, 4];

        let mut sub = Subgraph::new(&graph, subset);

        sub.add_to_subgraph(2);
    }

    #[test]
    #[should_panic]
    fn test_remove_from_subgraph_panic() {
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

        let subset = vec![0, 3, 4];

        let mut sub = Subgraph::new(&graph, subset);

        sub.remove_from_subgraph(6);
    }
}
