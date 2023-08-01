use crate::data_structures::{graph::Graph, subgraph::Subgraph};

use rand::{seq::IteratorRandom, thread_rng};
use std::{
    fs::File,
    io::{Error, Write},
};

pub fn dot_graph(graph: &Graph, filename: &str, subgraphs: Vec<Subgraph>) -> Result<(), Error> {
    let mut graph_string = String::from("graph {\n");
    let mut already_written: Vec<(usize, usize)> = Vec::new();
    let mut nodes_visited: Vec<bool> = vec![false; graph.nodes.len()];
    let available_colors = ["red", "green", "blue", "yellow", "orange", "purple"];
    graph.edges.iter().enumerate().for_each(|(i, e)| {
        e.iter().for_each(|j| {
            if !already_written.contains(&(i, *j)) && !already_written.contains(&(*j, i)) {
                already_written.push((i, *j));
                nodes_visited[i] = true;
                nodes_visited[*j] = true;
                graph_string.push_str(&format!("\t{} -- {};\n", i, j));
            }
        })
    });

    nodes_visited
        .iter()
        .enumerate()
        .filter(|v| !*v.1)
        .map(|(i, _)| i)
        .for_each(|v| graph_string.push_str(&format!("\t{};\n", v)));

    subgraphs.iter().enumerate().for_each(|(i, sg)| {
        let color = available_colors.iter().choose(&mut thread_rng()).unwrap();
        graph_string.push_str(&format!("\tsubgraph cluster_{} {{\n\t\tstyle=invis;\n", i));
        sg.subset.iter_1().for_each(|v| {
            graph_string.push_str(&format!("\t\t{} [fillcolor={}, style=filled];\n", v, color));
        });
        graph_string.push_str("\t}\n");
    });

    graph_string.push('}');
    File::create(filename)?.write_all(graph_string.as_bytes())?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::data_structures::{choice_dict::ChoiceDict, subgraph::Subgraph};

    #[test]
    #[cfg(not(miri))]
    fn test_dot_graph() {
        use super::dot_graph;
        use crate::data_structures::graph::Graph;
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

        let mut subset1 = ChoiceDict::new(graph.nodes.len());
        subset1.set(1);
        subset1.set(2);

        let sub = Subgraph::new(&graph, subset);
        let sub1 = Subgraph::new(&graph, subset1);
        dot_graph(&graph, "test.dot", vec![sub, sub1]).unwrap();
    }
}
