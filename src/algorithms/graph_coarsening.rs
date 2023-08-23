use std::collections::HashSet;

use crate::algorithms::bfs::ChoiceDictBFS;
use crate::data_structures::choice_dict::ChoiceDict;
use crate::data_structures::graph::Graph;
use crate::data_structures::subgraph::Subgraph;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum CloudType {
    Big,
    Critical,
    Small,
    Bridge,
    Leaf,
}

pub struct CPStructure<'a> {
    start: ChoiceDict,
    big: ChoiceDict,
    small: ChoiceDict,
    leaf: ChoiceDict,
    bridge: ChoiceDict,
    critical: ChoiceDict,
    g_1: Graph,
    g: &'a Graph,
}

impl<'b> CPStructure<'b> {
    fn new_empty(graph: &'b Graph) -> Self {
        CPStructure {
            start: ChoiceDict::new(graph.nodes.len()),
            big: ChoiceDict::new(graph.nodes.len()),
            small: ChoiceDict::new(graph.nodes.len()),
            leaf: ChoiceDict::new(graph.nodes.len()),
            bridge: ChoiceDict::new(graph.nodes.len()),
            critical: ChoiceDict::new(graph.nodes.len()),
            g_1: graph.clone(),
            g: graph,
        }
    }

    pub fn new(graph: &'b Graph) -> Self {
        let mut cloud_part = Self::new_empty(graph);
        cloud_part.cloud_partition(graph, &mut ChoiceDict::new(graph.nodes.len()));

        cloud_part
    }

    pub fn r#type(&self, v: usize) -> CloudType {
        if self.big.get(v) == 1 {
            return CloudType::Big;
        }
        if self.leaf.get(v) == 1 {
            return CloudType::Leaf;
        }
        if self.bridge.get(v) == 1 {
            return CloudType::Bridge;
        }
        if self.critical.get(v) == 1 {
            return CloudType::Critical;
        }
        panic!("something went wrong constructing leaf, critical and bridge")
    }

    pub fn cloud(&self, v: usize) -> Subgraph {
        let mut subset = ChoiceDict::new(self.g.nodes.len());
        ChoiceDictBFS::new(&self.g_1, v).for_each(|n| subset.set(n));
        Subgraph::new(self.g, subset)
    }

    pub fn border(&self, v: usize, u: usize) -> bool {
        self.g_1.neighbors(v).contains(&u)
    }

    fn adjacent_small_clouds(&self, subgraph: &Subgraph<'_>) -> Vec<Subgraph> {
        let mut neighbors = HashSet::new();
        let mut neighboring_clouds = Vec::new();
        for node in subgraph.subset.iter_1() {
            self.g
                .neighbors(node)
                .iter()
                .filter(|n| subgraph.subset.get(**n) != 1)
                .for_each(|n| {
                    neighbors.insert(n);
                })
        }

        neighbors
            .iter()
            .filter(|n| self.small.get(***n) == 1)
            .for_each(|n| {
                if !neighboring_clouds.contains(&self.cloud(**n)) {
                    neighboring_clouds.push(self.cloud(**n))
                }
            });

        neighboring_clouds
    }

    fn construct_critical_leaf_bridge(&mut self) {
        let mut leaf = ChoiceDict::new(self.g.nodes.len());
        let mut bridge = ChoiceDict::new(self.g.nodes.len());
        let mut critical = ChoiceDict::new(self.g.nodes.len());
        for n in self.start.iter_1().filter(|n| self.big.get(*n) == 1) {
            let cloud = self.cloud(n);

            for neighbor in self.adjacent_small_clouds(&cloud) {
                if self.critical.get(neighbor.subset.choice_1().unwrap()) == 1 {
                    continue;
                }

                for node in neighbor.subset.iter_1() {
                    if leaf.get(node) == 0 && bridge.get(node) == 0 {
                        leaf.set(node);
                    } else if leaf.get(node) == 1 {
                        leaf.remove(node);
                        bridge.set(node);
                    } else if bridge.get(node) == 1 {
                        bridge.remove(node);
                        critical.set(node);
                    }
                }
            }
        }
        self.leaf = leaf;
        self.bridge = bridge;
        self.critical = critical;
    }

    fn cloud_partition<'a>(&mut self, graph: &'a Graph, visited: &'a mut ChoiceDict) {
        let mut clouds = Vec::new();
        let mut working_graph = graph.clone();

        while let Some(node) = visited.choice_0() {
            self.start.set(node);
            let mut subgraph = Subgraph::new(graph, ChoiceDict::new(graph.nodes.len()));

            ChoiceDictBFS::new(&working_graph, node)
                .enumerate()
                .take_while(|(i, _)| ((*i + 1) as f32) <= (graph.nodes.len() as f32).log2())
                .map(|(_, n)| n)
                .for_each(|n| {
                    visited.set(n);
                    subgraph.add_to_subgraph(n);
                });

            if subgraph.subset.iter_1().count() >= (graph.nodes.len() as f32).log2() as usize {
                subgraph.subset.iter_1().for_each(|n| {
                    self.g.neighbors(n).iter().for_each(|neighbor| {
                        if subgraph.subset.get(*neighbor) == 0
                            && self.g_1.edges[n].contains(neighbor)
                        {
                            self.g_1.remove_edge((n, *neighbor));
                        }
                    })
                });
                subgraph.subset.iter_1().for_each(|n| self.big.set(n));
            } else {
                subgraph.subset.iter_1().for_each(|n| self.small.set(n));
            }

            subgraph
                .subset
                .iter_1()
                .for_each(|n| working_graph.remove_node(n));

            clouds.push(subgraph);
        }

        self.construct_critical_leaf_bridge();
    }
}

#[derive(Debug)]
pub struct F {
    f: Graph,
    node_to_cloud: Vec<usize>,
    cloud_to_node: Vec<usize>,
    weights: Vec<usize>,
}

impl F {
    fn new_empty(cloud_part: &CPStructure) -> Self {
        F {
            f: Graph::new(),
            node_to_cloud: Vec::new(),
            cloud_to_node: vec![usize::MAX; cloud_part.g.nodes.len()],
            weights: Vec::new(),
        }
    }
    pub fn new(cloud_part: &CPStructure) -> Self {
        let mut f = Self::new_empty(cloud_part);
        f.add_big_and_critical(cloud_part);
        f.add_edges_big_critical(cloud_part);
        f.add_meta_leaves(cloud_part);
        f
    }

    fn add_big_and_critical(&mut self, cloud_part: &CPStructure) {
        let mut x = ChoiceDict::new(cloud_part.g.nodes.len());
        let mut visited = ChoiceDict::new(cloud_part.g.nodes.len());
        let mut big_clouds: Vec<usize> = cloud_part.big.iter_1().collect();
        let mut critical_clouds: Vec<usize> = cloud_part.critical.iter_1().collect();
        while !big_clouds.is_empty() || !critical_clouds.is_empty() {
            let v = if big_clouds.is_empty() {
                critical_clouds[0]
            } else {
                big_clouds[0]
            };
            let cloud = cloud_part.cloud(v);
            cloud.subset.iter_1().for_each(|n| visited.set(n));
            if cloud_part.big.get(v) == 1 {
                big_clouds = cloud_part
                    .big
                    .iter_1()
                    .filter(|n| visited.get(*n) == 0)
                    .collect();
            }
            if cloud_part.critical.get(v) == 1 {
                critical_clouds = cloud_part
                    .big
                    .iter_1()
                    .filter(|n| visited.get(*n) == 0)
                    .collect();
            }

            self.f.add_node([].to_vec());
            self.weights.push(cloud.subset.iter_1().count());
            self.node_to_cloud.push(v);
            self.cloud_to_node[v] = self.f.nodes.len() - 1;
            x.set(v);
        }
    }

    pub fn add_edges_big_critical(&mut self, cloud_part: &CPStructure) {
        let mut completed = ChoiceDict::new(cloud_part.g.nodes.len());
        let mut discovered = ChoiceDict::new(cloud_part.g.nodes.len());

        while let Some(v) = completed
            .iter_0()
            .find(|n| cloud_part.big.get(*n) == 1 || cloud_part.critical.get(*n) == 1)
        {
            let cloud = cloud_part.cloud(v);
            cloud.subset.iter_1().for_each(|n| completed.set(n));

            let mut neighbors = Vec::new();
            cloud.subset.iter_1().for_each(|n| {
                cloud_part.g.neighbors(n).iter().for_each(|neighbor| {
                    if !neighbors.contains(neighbor) {
                        neighbors.push(*neighbor)
                    }
                })
            });

            neighbors.retain(|n| {
                cloud.subset.get(*n) == 0
                    && (cloud_part.big.get(*n) == 1 || cloud_part.critical.get(*n) == 1)
            });

            neighbors.iter().for_each(|n| {
                if discovered.get(*n) == 1 {
                    return;
                }
                let c_1 = cloud_part.cloud(*n);
                c_1.subset.iter_1().for_each(|w| discovered.set(w));
                let w = self.cloud_to_node[c_1.subset.iter_1().min().unwrap()];
                self.f.add_edge((w, self.cloud_to_node[v]));
            });

            discovered.reset();
        }
    }

    pub fn add_meta_leaves(&mut self, cloud_part: &CPStructure) {
        let mut completed = ChoiceDict::new(cloud_part.g.nodes.len());
        let mut discovered = ChoiceDict::new(cloud_part.g.nodes.len());

        while let Some(v) = completed
            .iter_0()
            .find(|n| cloud_part.big.get(*n) == 1 || cloud_part.critical.get(*n) == 1)
        {
            let cloud = cloud_part.cloud(v);
            cloud.subset.iter_1().for_each(|n| completed.set(n));

            let mut neighbors = Vec::new();
            cloud.subset.iter_1().for_each(|n| {
                cloud_part.g.neighbors(n).iter().for_each(|neighbor| {
                    if !neighbors.contains(neighbor) {
                        neighbors.push(*neighbor)
                    }
                })
            });

            neighbors.retain(|n| cloud.subset.get(*n) == 0 && cloud_part.leaf.get(*n) == 1);

            neighbors.iter().for_each(|n| {
                if discovered.get(*n) == 1 {
                    return;
                }
                let c_1 = cloud_part.cloud(*n);
                c_1.subset.iter_1().for_each(|w| discovered.set(w));
            });

            if discovered.choice_1().is_none() {
                continue;
            }

            let v_1 = discovered.iter_1().min().unwrap();

            self.cloud_to_node[v_1] = self.f.nodes.len() - 1;
            self.node_to_cloud.push(v_1);
            self.f.add_node([self.cloud_to_node[v_1]].to_vec());
            self.weights.push(discovered.iter_1().count());

            discovered.reset();
        }
    }

    pub fn add_meta_bridges(&mut self, cloud_part: &CPStructure) {
        let mut completed = ChoiceDict::new(cloud_part.g.nodes.len());
        let mut _discovered = ChoiceDict::new(cloud_part.g.nodes.len());
        let mut _g_a = cloud_part.g.clone();

        while let Some(v) = completed
            .iter_0()
            .find(|n| cloud_part.big.get(*n) == 1 || cloud_part.critical.get(*n) == 1)
        {
            let cloud = cloud_part.cloud(v);
            cloud.subset.iter_1().for_each(|n| completed.set(n));

            let g_b = self.construct_g_b(cloud_part, &cloud);

            let _b = cloud_part.cloud(
                g_b.subset
                    .iter_1()
                    .find(|n| cloud_part.bridge.get(*n) == 1)
                    .unwrap(),
            );

            //in gb: start at arbitrary bridge cloud, remove edges incident to b and c, traverse to C'
            //from C': explore all adjacent bridge clouds B, remove traversed edges and all edges adjacent to b from ga and gb
            //add meta bridge node to f and edges to C and C'
        }
    }

    fn construct_g_b(&self, _cloud_part: &CPStructure, _cloud: &Subgraph) -> Subgraph {
        //gb: graph induced by cloud, all bridge Clouds B adjacent to cloud, all big clouds connected to B
        todo!()
    }
}

#[cfg(test)]
mod tests {

    use std::fs;

    use crate::tools::graph_visualizer::dot_graph;

    use super::*;
    //use crate::tools::graph_visualizer::*;

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
                [8, 13].to_vec(),
                [9].to_vec(),
                [10, 17].to_vec(),
                [11, 16].to_vec(),
            ],
        );
        let cloud_part = CPStructure::new(&graph);
        let subgraphs: Vec<Subgraph> = cloud_part
            .start
            .iter_1()
            .map(|n| cloud_part.cloud(n))
            .collect();

        let cloud_p_dot = dot_graph(&graph, &subgraphs);
        fs::write("./cloud_part.dot", cloud_p_dot).unwrap();

        let f = F::new(&cloud_part);
        let f_dot = dot_graph(&f.f, &[]);
        fs::write("./f.dot", f_dot).unwrap();
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
