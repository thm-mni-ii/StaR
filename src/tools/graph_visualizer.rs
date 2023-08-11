use crate::data_structures::{graph::Graph, subgraph::Subgraph};

/// Generates a .dot file for the given graph. The subgraphs are colored in the order they are given.
///
/// # Example
/// ```
/// use star::data_structures::{graph::Graph, choice_dict::ChoiceDict, subgraph::Subgraph};
/// use star::tools::graph_visualizer::dot_graph;
/// let graph = Graph::new_with_edges(
///     6,
///     vec![
///         [3, 2].to_vec(),
///         [4, 2, 5].to_vec(),
///         [0, 1].to_vec(),
///         [0, 5].to_vec(),
///         [1].to_vec(),
///         [1, 3].to_vec(),
///     ],
/// );
/// let mut subset = ChoiceDict::new(graph.nodes.len());
/// subset.set(0);
/// subset.set(3);
/// subset.set(4);
/// let mut subset1 = ChoiceDict::new(graph.nodes.len());
/// subset1.set(1);
/// subset1.set(2);
/// let sub = Subgraph::new(&graph, subset);
/// let sub1 = Subgraph::new(&graph, subset1);
/// dot_graph(&graph, &[sub, sub1]);
/// ```

pub fn dot_graph(graph: &Graph, subgraphs: &[Subgraph]) -> String {
    let mut graph_string = String::from("graph {");
    let mut already_written: Vec<(usize, usize)> = Vec::new();
    let mut nodes_visited: Vec<bool> = vec![false; graph.nodes.len()];
    let available_colors = [
        "red",
        "green",
        "cadetblue1",
        "orange",
        "purple",
        "coral",
        "cyan",
        "darkolivegreen",
        "darkorchid",
        "darkseagreen",
        "deeppink",
        "gold",
        "hotpink",
        "indigo",
        "khaki",
        "lavender",
        "lightblue",
        "lightcoral",
        "lightcyan",
        "lightgray",
        "lightpink",
        "lightsalmon",
        "lightseagreen",
        "lightskyblue",
        "lightsteelblue",
        "magenta",
        "maroon",
        "mediumaquamarine",
        "mediumblue",
        "mediumorchid",
        "mediumpurple",
        "mediumseagreen",
        "mediumslateblue",
        "mediumspringgreen",
        "mediumturquoise",
        "mediumvioletred",
        "olivedrab",
        "orangered",
        "orchid",
        "palegreen",
        "paleturquoise",
        "palevioletred",
        "peru",
        "pink",
        "plum",
        "powderblue",
        "rebeccapurple",
        "rosybrown",
        "royalblue",
        "saddlebrown",
        "salmon",
        "sandybrown",
        "seagreen",
        "sienna",
        "skyblue",
        "slateblue",
        "springgreen",
        "steelblue",
        "tan",
        "teal",
        "tomato",
        "turquoise",
        "violet",
        "wheat",
        "yellowgreen",
    ];
    graph.edges.iter().enumerate().for_each(|(i, e)| {
        e.iter().for_each(|j| {
            if !already_written.contains(&(i, *j)) && !already_written.contains(&(*j, i)) {
                already_written.push((i, *j));
                nodes_visited[i] = true;
                nodes_visited[*j] = true;
                graph_string.push_str(&format!("{} -- {};", i, j));
            }
        })
    });

    nodes_visited
        .iter()
        .enumerate()
        .filter(|v| !*v.1)
        .map(|(i, _)| i)
        .for_each(|v| graph_string.push_str(&format!("{};", v)));

    subgraphs.iter().enumerate().for_each(|(i, sg)| {
        let color = available_colors[i % available_colors.len()];
        graph_string.push_str(&format!("subgraph cluster_{} {{style=invis;", i));
        sg.subset.iter_1().for_each(|v| {
            graph_string.push_str(&format!("{} [fillcolor={}, style=filled];", v, color));
        });
        graph_string.push('}');
    });

    println!("subgraphs processed");

    graph_string.push('}');

    graph_string
}

mod tests {

    #[test]
    fn test_dot_graph() {
        use super::dot_graph;
        use crate::data_structures::graph::Graph;
        use crate::data_structures::{choice_dict::ChoiceDict, subgraph::Subgraph};
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
        assert_eq!(dot_graph(&graph, &[sub, sub1]), "graph {0 -- 3;0 -- 2;1 -- 4;1 -- 2;5;subgraph cluster_0 {style=invis;0 [fillcolor=red, style=filled];3 [fillcolor=red, style=filled];4 [fillcolor=red, style=filled];}subgraph cluster_1 {style=invis;1 [fillcolor=green, style=filled];2 [fillcolor=green, style=filled];}}");
    }
}
