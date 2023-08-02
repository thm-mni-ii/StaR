use crate::algorithms::bfs::ChoiceDictBFS;
use crate::data_structures::choice_dict::ChoiceDict;
use crate::data_structures::graph::Graph;
use crate::data_structures::subgraph::Subgraph;

pub fn coarsen_graph<'a>(graph: &'a Graph, visited: &'a mut ChoiceDict) -> Vec<Subgraph<'a>> {
    let mut subgraphs = Vec::new();
    let mut working_graph = graph.clone();

    while visited.choice_0().is_some() {
        let node = visited.choice_0();
        println!("node: {:?}", node);
        let mut cloud = Subgraph::new(graph, ChoiceDict::new(graph.nodes.len()));

        ChoiceDictBFS::new(&working_graph, node.unwrap())
            .enumerate()
            .take_while(|(i, _)| (*i as f32) < (graph.nodes.len() as f32).log2())
            .map(|(_, n)| n)
            .for_each(|n| {
                visited.set(n);
                cloud.add_to_subgraph(n);
            });

        cloud
            .subset
            .iter_1()
            .for_each(|n| working_graph.remove_node(n));

        subgraphs.push(cloud);
    }
    subgraphs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tools::graph_visualizer::*;

    #[test]
    pub fn test() {
        let graph = crate::data_structures::graph::Graph::new_with_edges(
            18,
            vec![
                [1, 6].to_vec(),
                [0, 2, 7].to_vec(),
                [1, 3, 8].to_vec(),
                [2, 4, 9].to_vec(),
                [3, 5, 10].to_vec(),
                [4, 11].to_vec(),
                [0, 7, 12].to_vec(),
                [1, 6, 8, 13].to_vec(),
                [2, 7, 9, 14].to_vec(),
                [3, 8, 10, 15].to_vec(),
                [4, 9, 11, 16].to_vec(),
                [5, 10, 17].to_vec(),
                [6, 13].to_vec(),
                [7, 12, 14].to_vec(),
                [8, 13, 15].to_vec(),
                [9, 14, 16].to_vec(),
                [10, 15, 17].to_vec(),
                [11, 16].to_vec(),
            ],
        );
        let mut binding = ChoiceDict::new(graph.nodes.len());
        let subs = coarsen_graph(&graph, &mut binding);
        let graph_str = dot_graph(&graph, &subs);
        println!(
            "{:?}",
            subs.iter()
                .map(|s| s.subset.iter_1().collect())
                .collect::<Vec<Vec<usize>>>()
        );
        std::fs::write("test.dot", graph_str).unwrap();
    }
}
