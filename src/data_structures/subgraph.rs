use super::{choice_dict::ChoiceDict, graph::Graph};

#[derive(Debug, PartialEq)]
/// Data structure representing Subgraphs
pub struct Subgraph<'a> {
    pub graph: &'a Graph,
    pub subset: ChoiceDict,
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
    pub fn new(graph: &'a Graph, subset: ChoiceDict) -> Self {
        Subgraph { graph, subset }
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

        self.subset.set(node);
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

        self.subset.remove(node);
    }

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
    pub fn neighbors(&self, node: usize) -> Vec<usize> {
        if self.subset.get(node) == 0 {
            panic!("node {} is not part of the subgraph", node);
        }

        self.graph
            .neighbors(node)
            .iter()
            .filter(|n| self.subset.get(**n) == 1)
            .copied()
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
    pub fn get_nodes(&self) -> Vec<usize> {
        self.graph
            .nodes
            .iter()
            .enumerate()
            .map(|n| n.0)
            .filter(|n| self.subset.get(*n) == 1)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::data_structures::{choice_dict::ChoiceDict, graph::Graph};

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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        subset.set(0);
        subset.set(3);
        subset.set(4);

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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        subset.set(0);
        subset.set(3);
        subset.set(4);

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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        subset.set(0);
        subset.set(3);
        subset.set(4);

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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        subset.set(0);
        subset.set(3);
        subset.set(4);

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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        subset.set(0);
        subset.set(3);
        subset.set(4);

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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        subset.set(0);
        subset.set(3);
        subset.set(4);

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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        subset.set(0);
        subset.set(3);
        subset.set(4);

        let mut sub = Subgraph::new(&graph, subset);

        sub.add_to_subgraph(6);
    }

    #[test]
    #[should_panic]
    fn test_add_to_subgraph_panic_deleted() {
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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        graph.remove_node(2);
        subset.set(0);
        subset.set(3);
        subset.set(4);

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

        let mut subset = ChoiceDict::new(graph.nodes.len());
        subset.set(0);
        subset.set(3);
        subset.set(4);

        let mut sub = Subgraph::new(&graph, subset);

        sub.remove_from_subgraph(6);
    }
}
