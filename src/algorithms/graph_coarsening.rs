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

#[derive(Debug)]
pub struct CloudPartition<'a> {
    start: ChoiceDict,
    big: ChoiceDict,
    small: ChoiceDict,
    leaf: ChoiceDict,
    bridge: ChoiceDict,
    critical: ChoiceDict,
    g_1: Graph,
    g: &'a Graph,
}

impl<'b> CloudPartition<'b> {
    fn new_empty(graph: &'b Graph) -> Self {
        CloudPartition {
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
        if self.small.get(v) == 1 {
            return CloudType::Small;
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

    fn adjacent_clouds(&self, subgraph: &Subgraph<'_>, c_type: Vec<CloudType>) -> Vec<usize> {
        let mut neighbors = Vec::new();
        for node in subgraph.subset.iter_1() {
            self.g
                .neighbors(node)
                .iter()
                .filter(|n| subgraph.subset.get(**n) != 1 && c_type.contains(&self.r#type(**n)))
                .for_each(|n| {
                    neighbors.push(*n);
                })
        }
        neighbors
    }

    fn construct_critical_leaf_bridge(&mut self) {
        let mut leaf = ChoiceDict::new(self.g.nodes.len());
        let mut bridge = ChoiceDict::new(self.g.nodes.len());
        let mut critical = ChoiceDict::new(self.g.nodes.len());
        for n in self.start.iter_1().filter(|n| self.big.get(*n) == 1) {
            let cloud = self.cloud(n);

            for neighbor in self.adjacent_clouds(&cloud, vec![CloudType::Small]) {
                if self.critical.get(neighbor) == 1 {
                    continue;
                }
                let c = self.cloud(neighbor);

                for node in c.subset.iter_1() {
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
        while let Some(node) = visited.choice_0() {
            self.start.set(node);
            let mut subgraph = Vec::new();

            ChoiceDictBFS::new(&self.g_1, node)
                .enumerate()
                .take_while(|(i, _)| ((*i + 1) as f32) <= (graph.nodes.len() as f32).log2())
                .map(|(_, n)| n)
                .for_each(|n| {
                    visited.set(n);
                    subgraph.push(n);
                });

            if subgraph.len() >= (graph.nodes.len() as f32).log2() as usize {
                subgraph.iter().for_each(|n| {
                    self.g.neighbors(*n).iter().for_each(|neighbor| {
                        if !subgraph.contains(neighbor) {
                            self.g_1.remove_edge((*n, *neighbor));
                        }
                    })
                });
                subgraph.iter().for_each(|n| self.big.set(*n));
            } else {
                subgraph.iter().for_each(|n| self.small.set(*n));
            }
        }

        self.construct_critical_leaf_bridge();
    }
}

#[derive(Debug)]
pub struct F<'a> {
    f: Graph,
    node_to_cloud: Vec<usize>,
    cloud_to_node: Vec<usize>,
    weights: Vec<usize>,
    cloud_part: &'a CloudPartition<'a>,
}

impl<'a> F<'a> {
    fn new_empty(cloud_part: &'a CloudPartition) -> Self {
        F {
            f: Graph::new(),
            node_to_cloud: Vec::new(),
            cloud_to_node: vec![usize::MAX; cloud_part.g.nodes.len()],
            weights: Vec::new(),
            cloud_part,
        }
    }

    pub fn new(cloud_part: &'a CloudPartition) -> Self {
        let mut f = Self::new_empty(cloud_part);
        f.add_big_and_critical();
        f.add_edges_big_critical();
        f.add_meta_leaves();
        f.add_meta_bridges();
        f
    }

    pub fn expand(&self, v: usize) -> Subgraph<'a> {
        match self.cloud_part.r#type(v) {
            CloudType::Big | CloudType::Critical => self.cloud_part.cloud(self.node_to_cloud[v]),
            CloudType::Bridge => self.expand_leaf(v),
            CloudType::Leaf => self.expand_bridge(v),
            _ => panic!("something went wrong constructing bridge, leaf and critical"),
        }
    }

    fn expand_leaf(&self, v: usize) -> Subgraph<'a> {
        let mut g_leaf = self.cloud_part.cloud(self.node_to_cloud[v]);
        let c = self.cloud_part.cloud(
            *g_leaf
                .subset
                .iter_1()
                .flat_map(|n| self.cloud_part.g.neighbors(n))
                .find(|n| g_leaf.subset.get(**n) == 0)
                .unwrap(),
        );

        c.subset.iter_1().for_each(|n| g_leaf.add_to_subgraph(n));

        self.cloud_part
            .adjacent_clouds(&c, vec![CloudType::Leaf])
            .iter()
            .for_each(|neighbor| {
                if g_leaf.subset.get(*neighbor) == 1 {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*neighbor);
                c_1.subset.iter_1().for_each(|n| g_leaf.add_to_subgraph(n));
            });

        g_leaf
    }

    fn expand_bridge(&self, _v: usize) -> Subgraph<'a> {
        // create f' that contains big nodes and an edge between two nodes when there is a meta bridge connecting these nodes
        //split each edge: adding corresponding meta bridge, direct edges towards direction of original edge
        todo!()
    }

    fn add_big_and_critical(&mut self) {
        let mut x = ChoiceDict::new(self.cloud_part.g.nodes.len());
        let mut visited = ChoiceDict::new(self.cloud_part.g.nodes.len());
        let mut big_clouds: Vec<usize> = self.cloud_part.big.iter_1().collect();
        let mut critical_clouds: Vec<usize> = self.cloud_part.critical.iter_1().collect();
        while !big_clouds.is_empty() || !critical_clouds.is_empty() {
            let v = if big_clouds.is_empty() {
                critical_clouds[0]
            } else {
                big_clouds[0]
            };
            let cloud = self.cloud_part.cloud(v);
            cloud.subset.iter_1().for_each(|n| visited.set(n));
            if self.cloud_part.r#type(v) == CloudType::Big {
                big_clouds = self
                    .cloud_part
                    .big
                    .iter_1()
                    .filter(|n| visited.get(*n) == 0)
                    .collect();
            }
            if self.cloud_part.r#type(v) == CloudType::Critical {
                critical_clouds = self
                    .cloud_part
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

    pub fn add_edges_big_critical(&mut self) {
        let mut completed = ChoiceDict::new(self.cloud_part.g.nodes.len());
        let mut discovered = ChoiceDict::new(self.cloud_part.g.nodes.len());

        while let Some(v) = completed
            .iter_0()
            .find(|n| self.cloud_part.big.get(*n) == 1 || self.cloud_part.critical.get(*n) == 1)
        {
            let cloud = self.cloud_part.cloud(v);
            cloud.subset.iter_1().for_each(|n| completed.set(n));

            let neighbors = self
                .cloud_part
                .adjacent_clouds(&cloud, vec![CloudType::Big, CloudType::Critical]);

            neighbors.iter().for_each(|n| {
                if discovered.get(*n) == 1 {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*n);
                c_1.subset.iter_1().for_each(|w| discovered.set(w));
                let w = self.cloud_to_node[c_1.subset.iter_1().min().unwrap()];
                self.f.add_edge((w, self.cloud_to_node[v]));
            });

            discovered.reset();
        }
    }

    pub fn add_meta_leaves(&mut self) {
        let mut completed = ChoiceDict::new(self.cloud_part.g.nodes.len());
        let mut discovered = ChoiceDict::new(self.cloud_part.g.nodes.len());

        while let Some(v) = completed.iter_0().find(|n| {
            self.cloud_part.r#type(*n) == CloudType::Big
                || self.cloud_part.r#type(*n) == CloudType::Critical
        }) {
            let cloud = self.cloud_part.cloud(v);
            cloud.subset.iter_1().for_each(|n| completed.set(n));

            let neighbors = self
                .cloud_part
                .adjacent_clouds(&cloud, vec![CloudType::Leaf]);

            neighbors.iter().for_each(|n| {
                if discovered.get(*n) == 1 {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*n);
                c_1.subset.iter_1().for_each(|w| discovered.set(w));
            });

            if discovered.choice_1().is_none() {
                continue;
            }

            let v_1 = discovered.iter_1().min().unwrap();

            self.cloud_to_node[v_1] = self.f.nodes.len() - 1;
            self.node_to_cloud.push(v_1);
            self.f
                .add_node([self.cloud_to_node[cloud.subset.iter_1().min().unwrap()]].to_vec());
            self.weights.push(discovered.iter_1().count());

            discovered.reset();
        }
    }

    pub fn add_meta_bridges(&mut self) {
        let mut completed = ChoiceDict::new(self.cloud_part.g.nodes.len());
        let mut discovered = ChoiceDict::new(self.cloud_part.g.nodes.len());
        //let mut _g_a = cloud_part.g.clone();

        while let Some(v) = completed
            .iter_0()
            .find(|n| self.cloud_part.big.get(*n) == 1 || self.cloud_part.critical.get(*n) == 1)
        {
            let cloud = self.cloud_part.cloud(v);
            cloud.subset.iter_1().for_each(|n| completed.set(n));

            let mut g_b = self.construct_g_b(self.cloud_part, &cloud);

            while let Some(b_1) = discovered
                .iter_0()
                .find(|n| g_b.nodes[*n] == 0 && self.cloud_part.r#type(*n) == CloudType::Bridge)
            {
                let b = self.cloud_part.cloud(b_1);
                //remove all edges incident to b AND c
                b.subset.iter_1().for_each(|n_b| {
                    let neighbors: Vec<usize> = g_b
                        .neighbors(n_b)
                        .iter()
                        .filter(|neighbor| cloud.subset.get(**neighbor) == 1)
                        .copied()
                        .collect();
                    for neighbor in neighbors {
                        g_b.remove_edge((n_b, neighbor))
                    }
                });

                //traverse to c'
                let c_1_start = g_b
                    .nodes
                    .iter()
                    .enumerate()
                    .filter(|(_, x)| **x == 0)
                    .map(|(i, _)| i)
                    .find(|n| {
                        self.cloud_part.r#type(*n) != CloudType::Bridge
                            && cloud.subset.get(*n) == 0
                            && b.subset.get(*n) == 0
                    })
                    .unwrap();

                let c_dash = self.cloud_part.cloud(c_1_start);
                let mut weight = 0_usize;

                //explore all adjacent bridge clouds
                let adjacent_bridge_clouds = self
                    .cloud_part
                    .adjacent_clouds(&c_dash, vec![CloudType::Bridge])
                    .iter()
                    .map(|n| self.cloud_part.cloud(*n))
                    .collect::<Vec<Subgraph>>();

                // ab hier Implementierung nicht ganz nach Paper
                let w_1 = adjacent_bridge_clouds
                    .iter()
                    .flat_map(|s: &Subgraph| s.subset.iter_1())
                    .min()
                    .unwrap();

                for bridge in adjacent_bridge_clouds {
                    for node in bridge.subset.iter_1() {
                        discovered.set(node)
                    }
                    weight += bridge.subset.iter_1().count();
                }
                //ab hier wieder nach Paper

                let u_1 = self.cloud_to_node[cloud.subset.iter_1().min().unwrap()];
                let v_1 = self.cloud_to_node[c_dash.subset.iter_1().min().unwrap()];
                self.f.add_node([v_1, u_1].to_vec());
                self.weights.push(weight);
                self.node_to_cloud.push(w_1);
                self.cloud_to_node[w_1] = self.f.nodes.len() - 1;
            }

            //from C': remove traversed edges and all edges adjacent to b from ga and gb
            //add meta bridge node to f and edges to C and C'
        }
    }

    fn construct_g_b(&'a self, cloud_part: &'a CloudPartition, cloud: &Subgraph) -> Graph {
        let mut sub = Subgraph::new(cloud_part.g, ChoiceDict::new(cloud_part.g.nodes.len()));
        cloud.subset.iter_1().for_each(|n| sub.add_to_subgraph(n));

        let mut clouds = vec![cloud.subset.choice_1().unwrap()];

        while let Some(c) = clouds.pop() {
            let c_cloud = cloud_part.cloud(c);
            let mut neighbors;

            if cloud_part.r#type(c) == CloudType::Bridge {
                neighbors = self.cloud_part.adjacent_clouds(
                    &c_cloud,
                    vec![CloudType::Bridge, CloudType::Critical, CloudType::Big],
                );
                neighbors.retain(|n| sub.subset.get(*n) == 0);
            } else {
                neighbors = self
                    .cloud_part
                    .adjacent_clouds(&c_cloud, vec![CloudType::Bridge]);
                neighbors.retain(|n| sub.subset.get(*n) == 0);
            }

            for n in neighbors {
                let c_1 = cloud_part.cloud(n);
                c_1.subset.iter_1().for_each(|n| sub.add_to_subgraph(n));

                if cloud_part.r#type(c_1.subset.choice_1().unwrap()) == CloudType::Bridge {
                    clouds.push(c_1.subset.choice_1().unwrap());
                }
            }
        }

        let mut g_b = cloud_part.g.clone();

        for n in 0..g_b.nodes.len() {
            if sub.subset.get(n) == 0 {
                g_b.remove_node(n);
            }
        }
        g_b
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
        let g_dot = dot_graph(&graph, &[]);
        fs::write("./g.dot", g_dot).unwrap();

        let cloud_part = CloudPartition::new(&graph);
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
        //println!("{:?}", f.expand(15).subset.iter_1().collect::<Vec<usize>>());
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
