use crate::data_structures::graph::Graph;

const AVAILABLE_COLORS: [&str; 63] = [
    "red",
    "green",
    "cadetblue1",
    "orange",
    "purple",
    "coral",
    "darkolivegreen",
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
/// Generates a .dot file for the given graph. The subgraphs are colored in the order they are given.
///
/// # Example
/// ```
/// use star::data_structures::graph::Graph;
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
/// let mut subset = vec![0, 3, 4];
/// let mut subset1 = vec![1, 2];
/// dot_graph(&graph, &[subset, subset1]);
/// ```

pub fn dot_graph(graph: &Graph, subgraphs: &[Vec<usize>]) -> String {
    let mut graph_string = String::from("graph {");
    let mut already_written: Vec<(usize, usize)> = Vec::new();
    let mut nodes_visited: Vec<bool> = vec![false; graph.nodes];
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
        let color = AVAILABLE_COLORS[i % AVAILABLE_COLORS.len()];
        graph_string.push_str(&format!("subgraph cluster_{} {{style=invis;", i));
        sg.iter().for_each(|v| {
            graph_string.push_str(&format!("{} [fillcolor={}, style=filled];", v, color));
        });
        graph_string.push('}');
    });

    graph_string.push('}');

    graph_string
}

mod tests {

    #[test]
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
        let subset = vec![0, 3, 4];

        let subset1 = vec![1, 2];
        assert_eq!(dot_graph(&graph, &[subset, subset1]), "graph {0 -- 3;0 -- 2;1 -- 4;1 -- 2;5;subgraph cluster_0 {style=invis;0 [fillcolor=red, style=filled];3 [fillcolor=red, style=filled];4 [fillcolor=red, style=filled];}subgraph cluster_1 {style=invis;1 [fillcolor=green, style=filled];2 [fillcolor=green, style=filled];}}");
    }
}
