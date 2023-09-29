use crate::data_structures::choice_dict::ChoiceDict;
use std::collections::VecDeque;

pub trait GraphLike {
    fn neighbors(&self, node: usize) -> Vec<usize>;
    fn get_nodes(&self) -> Vec<usize>;
}
/// An iterator iterating over nodes of a graph in a breadth-first-search order
pub struct StandardBFS<'a, T: GraphLike> {
    start: Option<usize>,
    graph: &'a T,
    visited: Vec<bool>,
    queue: VecDeque<usize>,
}

impl<'a, G> Iterator for StandardBFS<'a, G>
where
    G: GraphLike,
{
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start.is_some() {
            self.visited[self.start.unwrap()] = true;
            self.queue.push_back(self.start.unwrap());
            self.start = None;
        }

        if self.queue.is_empty() {
            return None;
        }
        let temp = self.queue.pop_front().unwrap();
        //self.visited[temp] = true;
        let neighbors = self.graph.neighbors(temp);

        for n in neighbors {
            if !self.visited[n] {
                self.visited[n] = true;
                self.queue.push_back(n);
            }
        }

        Some(temp)
    }
}

impl<'a, G> StandardBFS<'a, G>
where
    G: GraphLike,
{
    /// Returns a new Standard BFS iterator. Takes a reference to a graph and a starting node.
    ///
    /// Time complexity for the entire BFS: O(n)
    /// # Example
    /// ```
    /// use star::algorithms::bfs::StandardBFS;
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///     ],
    /// );
    ///
    ///  StandardBFS::new(&graph, 0);
    /// ```

    pub fn new(graph: &'a G, start: usize) -> Self {
        Self {
            start: Some(start),
            graph,
            queue: VecDeque::new(),
            visited: vec![false; graph.get_nodes().len()],
        }
    }
}

//----------------------------------------------------------------

pub struct ChoiceDictBFS<'a, G> {
    start: usize,
    start_needed: bool,
    node_with_neighbors_left: Option<usize>,
    graph: &'a G,
    colors: ChoiceDict,
    colors_2: ChoiceDict,
}

/// An iterator iterating over nodes of a graph in a breadth-first-search order. Takes less space than a standard BFS. Based on: https://arxiv.org/pdf/1812.10950.pdf
impl<'a, G> Iterator for ChoiceDictBFS<'a, G>
where
    G: GraphLike,
{
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start_needed {
            self.colors.set(self.start);
            self.colors_2.set(self.start);
            self.start_needed = false;

            return Some(self.start);
        }

        let mut current_node = self.node_with_neighbors_left;

        if self.node_with_neighbors_left.is_none() {
            current_node = self.colors_2.choice_1();
            current_node?;
        }

        let node = current_node.unwrap();
        let mut ret: Option<usize> = None;

        if node == self.start
            || self.graph.neighbors(node).iter().any(|neighbor| {
                self.colors_2.get(*neighbor) == 0 && self.colors.get(*neighbor) == 1
            })
        {
            self.node_with_neighbors_left = Some(node);
            for neighbor in self.graph.neighbors(node) {
                if self.colors.get(neighbor) == 0 {
                    self.colors.set(neighbor);
                    self.colors_2.set(neighbor);
                    ret = Some(neighbor);
                    break;
                }
            }
        }

        if !self
            .graph
            .neighbors(node)
            .iter()
            .any(|neighbor| self.colors.get(*neighbor) == 0)
        {
            self.colors.set(node);
            self.colors_2.remove(node);
            self.node_with_neighbors_left = None;
        }

        if ret.is_some() {
            return ret;
        }

        self.next()
    }
}

impl<'a, G> ChoiceDictBFS<'a, G>
where
    G: GraphLike,
{
    /// Returns a new BFS iterator using Choice Dictionaries. Takes a reference to a graph and a starting node.
    ///
    /// Time complexity for the entire BFS: O(n+m), Space complexity: n * log(3) + O(log(n)^2)
    /// # Example
    /// ```
    /// use star::algorithms::bfs::ChoiceDictBFS;
    /// use star::data_structures::graph::Graph;
    /// let graph = Graph::new_with_edges(
    ///     2,
    ///     vec![
    ///         [0].to_vec(),
    ///         [1].to_vec(),
    ///     ],
    /// );
    ///
    ///  ChoiceDictBFS::new(&graph, 0);
    /// ```

    pub fn new(graph: &'a G, start: usize) -> Self {
        Self {
            start,
            start_needed: true,
            node_with_neighbors_left: None,
            graph,
            colors: ChoiceDict::new(graph.get_nodes().len()),
            colors_2: ChoiceDict::new(graph.get_nodes().len()),
        }
    }
}

#[cfg(test)]
mod tests {
    //TODO: Tests mit Subgraphen
    use crate::{
        algorithms::bfs::{ChoiceDictBFS, StandardBFS},
        data_structures::graph::Graph,
    };

    #[test]
    fn test_whole() {
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
            StandardBFS::new(&graph, 0).collect::<Vec<usize>>(),
            [0, 3, 2, 1, 4]
        );
        assert_eq!(
            ChoiceDictBFS::new(&graph, 0).collect::<Vec<usize>>(),
            [0, 3, 2, 1, 4]
        );
    }

    #[test]
    fn test_whole_preprocess_other_start() {
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
            StandardBFS::new(&graph, 2).collect::<Vec<usize>>(),
            [2, 0, 1, 3, 4]
        );
        assert_eq!(
            ChoiceDictBFS::new(&graph, 2).collect::<Vec<usize>>(),
            [2, 0, 1, 3, 4]
        );
    }
}
