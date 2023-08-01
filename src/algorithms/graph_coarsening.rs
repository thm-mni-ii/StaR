use crate::algorithms::bfs::ChoiceDictBFS;
use crate::data_structures::choice_dict::ChoiceDict;
use crate::data_structures::graph::Graph;
use crate::data_structures::subgraph::Subgraph;

pub struct GraphCoarsening<'a> {
    graph: &'a Graph,
    visited: ChoiceDict,
}

impl<'a> GraphCoarsening<'a> {
    pub fn new(graph: &'a Graph) -> Self {
        Self {
            graph,
            visited: ChoiceDict::new(graph.nodes.len()),
        }
    }

    pub fn coarsen_graph(&mut self) {
        while self.visited.choice_0().is_some() {
            let node = self.visited.choice_0();
            println!(
                "{:?}",
                self.find_cloud(node.unwrap())
                    .subset
                    .iter_1()
                    .collect::<Vec<usize>>()
            );
        }
    }

    pub fn find_cloud(&mut self, starting_node: usize) -> Subgraph {
        let mut cloud = Subgraph::new(self.graph, ChoiceDict::new(self.graph.nodes.len()));
        ChoiceDictBFS::new(self.graph, starting_node)
            .enumerate()
            .filter(|(i, _)| (*i as f32) < (self.graph.nodes.len() as f32).log2())
            .map(|(_, n)| n)
            .for_each(|n| {
                self.visited.set(n);
                cloud.add_to_subgraph(n);
            });
        cloud
    }
}

#[cfg(test)]
mod tests {
    use super::GraphCoarsening;

    #[test]
    pub fn test() {
        let graph = crate::data_structures::graph::Graph::new_with_edges(
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
        let mut gc = GraphCoarsening::new(&graph);
        gc.coarsen_graph();
    }
}
