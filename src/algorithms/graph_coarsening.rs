use core::num;
use std::collections::HashSet;

use crate::algorithms::bfs::ChoiceDictBFS;
use crate::data_structures::choice_dict::ChoiceDict;
use crate::data_structures::graph::Graph;
use crate::data_structures::subgraph::Subgraph;

#[derive(Debug, PartialEq, Clone, Copy)]
enum CloudType {
    Big,
    Critical,
    Small,
    Bridge,
    Leaf,
}

pub struct CloudGraph<'a> {
    clouds: Vec<Cloud<'a>>,
    edges: Vec<Vec<usize>>,
}

impl CloudGraph<'_> {
    pub fn new(clouds: Vec<Cloud<'_>>, edges: Vec<Vec<usize>>) -> CloudGraph<'_> {
        CloudGraph { clouds, edges }
    }
}

pub struct Cloud<'a> {
    nodes: Subgraph<'a>,
    c_type: CloudType,
}

impl Cloud<'_> {
    fn new(nodes: Subgraph<'_>, c_type: CloudType) -> Cloud<'_> {
        Cloud { nodes, c_type }
    }
}

pub fn build_cloud_graph<'a>(subgraphs: &'a Vec<Subgraph<'a>>, graph: &'a Graph) -> CloudGraph<'a> {
    let mut neighbors = Vec::new();
    let mut cloud_types = Vec::new();
    let mut clouds = Vec::new();

    subgraphs.iter().enumerate().for_each(|(i, s)| {
        cloud_types.push(cloud_type(s, graph, &neighbors[i]));
    });

    subgraphs.iter().enumerate().for_each(|(i, s)| {
        clouds.push(Cloud::new(s.clone(), cloud_types[i]));
    });

    for i in 0..subgraphs.len() {
        neighbors.push(set_cloud_neighbors(&subgraphs[i], subgraphs, graph));
    }

    CloudGraph::new(clouds, neighbors)
}

fn set_cloud_neighbors<'a>(
    subgraph: &'a Subgraph<'a>,
    all_subs: &'a [Subgraph<'a>],
    graph: &'a Graph,
) -> Vec<usize> {
    let mut neighbors = HashSet::new();
    let mut neighboring_clouds = Vec::new();
    for node in subgraph.subset.iter_1() {
        graph
            .neighbors(node)
            .iter()
            .filter(|n| subgraph.subset.get(**n) != 1)
            .for_each(|n| {
                neighbors.insert(n);
            })
    }

    neighbors.iter().for_each(|n| {
        let cloud_neighbor = all_subs
            .iter()
            .enumerate()
            .find(|(_, s)| s.subset.get(**n) == 1)
            .unwrap();
        if !neighboring_clouds.contains(&cloud_neighbor.0) {
            neighboring_clouds.push(cloud_neighbor.0);
        }
    });

    neighboring_clouds
}

fn cloud_type(subgraph: &Subgraph, graph: &Graph, cloud_neighbors: &Vec<usize>) -> CloudType {
    if subgraph.subset.iter_1().count() >= (graph.nodes.len() as f32).log2() as usize {
        return CloudType::Big;
    }
    if cloud_neighbors.len() >= 3 {
        return CloudType::Critical;
    }
    if cloud_neighbors.len() == 2 {
        return CloudType::Bridge;
    }
    if cloud_neighbors.len() == 1 {
        return CloudType::Leaf;
    }

    CloudType::Small
}
//}

pub fn cloud_partition<'a>(graph: &'a Graph, visited: &'a mut ChoiceDict) -> Vec<Subgraph<'a>> {
    let mut clouds = Vec::new();
    let mut working_graph = graph.clone();

    while let Some(node) = visited.choice_0() {
        let mut subgraph = Subgraph::new(graph, ChoiceDict::new(graph.nodes.len()));

        ChoiceDictBFS::new(&working_graph, node)
            .enumerate()
            .take_while(|(i, _)| (*i as f32) < (graph.nodes.len() as f32).log2())
            .map(|(_, n)| n)
            .for_each(|n| {
                visited.set(n);
                subgraph.add_to_subgraph(n);
            });

        subgraph
            .subset
            .iter_1()
            .for_each(|n| working_graph.remove_node(n));

        clouds.push(subgraph);
    }
    clouds
}

pub fn construct_f(clouds: &CloudGraph) -> (Graph, Vec<usize>) {
    let mut f = Graph::new();
    let mut weights = Vec::new();
    let mut big_clouds = Vec::new();
    let mut f_indices = vec![None; clouds.clouds.len()];

    for cloud in clouds.clouds.iter().enumerate() {
        if cloud.1.c_type == CloudType::Big || cloud.1.c_type == CloudType::Critical {
            f.add_node([].to_vec());
            weights.push(cloud.1.nodes.subset.iter_1().count());
            if cloud.1.c_type == CloudType::Big {
                big_clouds.push(cloud);
            }
            f_indices[cloud.0] = Some(f.nodes.len() - 1);
        }
    }

    add_edges(&mut f, f_indices, clouds);

    todo!("bridge clouds hinzufügen");

    big_clouds.iter().enumerate().for_each(|bc| {
        let number_leafs = clouds.edges[bc.0]
            .iter()
            .filter(|n| clouds.clouds[**n].c_type == CloudType::Leaf)
            .count();
        if number_leafs > 0 {
            f.add_node([bc.1 .0].to_vec());
            weights.push(number_leafs);
        }
    });

    (f, weights)
}

fn add_edges(f: &mut Graph, f_indices: Vec<Option<usize>>, graph: &CloudGraph) {
    graph
        .clouds
        .iter()
        .enumerate()
        .filter(|c| c.1.c_type == CloudType::Big || c.1.c_type == CloudType::Critical)
        .for_each(|(i, _)| {
            graph.edges[i]
                .iter()
                .for_each(|j| f.add_edge((f_indices[i].unwrap(), *j)))
        });
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
        /*let file = std::fs::File::open("tests/planar_embedding1000000.pg").unwrap();
        let buf_reader = std::io::BufReader::new(file);
        let graph = Graph::try_from(buf_reader).unwrap();*/
        println!("Graph loaded");
        let mut binding = ChoiceDict::new(graph.nodes.len());
        let subs = cloud_partition(&graph, &mut binding);
        println!("graph coarsened, {} subgraphs", subs.len());
        let graph_str = dot_graph(&graph, &Vec::new());
        println!("dot string created");
        std::fs::write("cloud_part.dot", graph_str).unwrap();
        let f = construct_f(&build_cloud_graph(&subs, &graph));
        let f_str = dot_graph(&f.0, &[]);
        std::fs::write("f.dot", f_str).unwrap();
    }

    #[test]
    pub fn test_choice_dict() {
        let mut choice_dict = ChoiceDict::new(1000);
        for i in 0..96 {
            choice_dict.set(i);
        }

        assert_eq!(choice_dict.get(999), 0);
        choice_dict.set(999);
        assert_eq!(choice_dict.get(999), 1);
    }
}
