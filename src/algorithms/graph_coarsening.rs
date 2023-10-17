use core::panic;

use crate::data_structures::{bitvec::FastBitvec, graph::Graph};

use super::bfs::StandardBFS;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum CloudType {
    Big,
    Critical,
    Small,
    Bridge,
    Leaf,
}

//TODO: Operationen wie add_edge, remove_edge, remove_node sollten eine unchecked Variante haben mit O(1) Laufzeit

#[derive(Debug)]
pub struct CloudPartition<'a> {
    start: FastBitvec,
    big: FastBitvec,
    small: FastBitvec,
    leaf: FastBitvec,
    bridge: FastBitvec,
    critical: FastBitvec,
    g_1: Graph,
    g: &'a Graph,
}

impl<'b> CloudPartition<'b> {
    fn new_empty(graph: &'b Graph) -> Self {
        CloudPartition {
            start: FastBitvec::new(graph.nodes + 1),
            big: FastBitvec::new(graph.nodes + 1),
            small: FastBitvec::new(graph.nodes + 1),
            leaf: FastBitvec::new(graph.nodes + 1),
            bridge: FastBitvec::new(graph.nodes + 1),
            critical: FastBitvec::new(graph.nodes + 1),
            g_1: graph.clone(),
            g: graph,
        }
    }

    pub fn new(graph: &'b Graph) -> Self {
        let mut cloud_part = Self::new_empty(graph);
        cloud_part.cloud_partition(graph, &mut FastBitvec::new(graph.nodes));

        cloud_part
    }

    pub fn cloud_type(&self, v: usize) -> CloudType {
        if self.big.get(v) {
            return CloudType::Big;
        }
        if self.leaf.get(v) {
            return CloudType::Leaf;
        }
        if self.bridge.get(v) {
            return CloudType::Bridge;
        }
        if self.critical.get(v) {
            return CloudType::Critical;
        }
        if self.small.get(v) {
            return CloudType::Small;
        }
        panic!("something went wrong constructing leaf, critical and bridge")
    }

    pub fn cloud(&self, v: usize) -> Vec<usize> {
        let mut visited = FastBitvec::new(self.g.nodes);
        StandardBFS::new(&self.g_1, v, &mut visited).collect()
    }

    pub fn border(&self, v: usize, u: usize) -> bool {
        self.g_1.neighbors(v).contains(&u)
    }

    fn construct_critical_leaf_bridge(&mut self) {
        let mut irrelevant_edges: Vec<FastBitvec> = self
            .g
            .edges
            .iter()
            .map(|n| FastBitvec::new(n.len()))
            .collect();
        let big_nodes = self
            .start
            .iter_1()
            .filter(|n| self.big.get(*n))
            .collect::<Vec<usize>>();
        for node in big_nodes {
            self.visit_big_cloud(
                &mut FastBitvec::new(self.g.nodes),
                &mut irrelevant_edges,
                node,
            );
        }
    }

    fn visit_big_cloud(
        &mut self,
        visited_big_clouds: &mut FastBitvec,
        irrelevant_edges: &mut [FastBitvec],
        n: usize,
    ) {
        for node in self.cloud(n) {
            visited_big_clouds.set(node, true);
        }
        for node in self.cloud(n) {
            for edge in self
                .g
                .neighbors(node)
                .iter()
                .enumerate()
                .collect::<Vec<(usize, &usize)>>()
            {
                if irrelevant_edges[node].get(edge.0) {
                    continue;
                }
                if self.small.get(*edge.1) {
                    self.visit_small_cloud(irrelevant_edges, visited_big_clouds, *edge.1);
                } else {
                    irrelevant_edges[node].set(edge.0, true);
                    irrelevant_edges[*edge.1].set(self.g.back_edges[node][edge.0], true);
                }
            }
        }
    }

    fn visit_small_cloud(
        &mut self,
        irrelevant_edges: &mut [FastBitvec],
        visited_big_clouds: &FastBitvec,
        n: usize,
    ) {
        for node in self.cloud(n) {
            if self.critical.get(node) {
                continue;
            }
            self.increase_node_level(node);
            for edge in self
                .g
                .neighbors(node)
                .iter()
                .enumerate()
                .collect::<Vec<(usize, &usize)>>()
            {
                if irrelevant_edges[node].get(edge.0) {
                    continue;
                }
                if self.big.get(*edge.1) {
                    if visited_big_clouds.get(*edge.1) {
                        irrelevant_edges[node].set(edge.0, true);
                        irrelevant_edges[*edge.1].set(self.g.back_edges[node][edge.0], true);
                    }
                } else {
                    irrelevant_edges[node].set(edge.0, true);
                    irrelevant_edges[*edge.1].set(self.g.back_edges[node][edge.0], true);
                }
            }
        }
    }

    fn increase_node_level(&mut self, node: usize) {
        match self.cloud_type(node) {
            CloudType::Bridge => {
                self.bridge.set(node, false);
                self.critical.set(node, true);
            }
            CloudType::Leaf => {
                self.leaf.set(node, false);
                self.bridge.set(node, true);
            }
            CloudType::Critical => {}
            CloudType::Small => self.leaf.set(node, true),
            _ => {}
        }
    }

    fn cloud_partition<'a>(&mut self, graph: &'a Graph, visited: &'a mut FastBitvec) {
        while let Some(node) = visited.choice_0() {
            //println!("node: {}", node);
            self.start.set(node, true);
            let mut subgraph = Vec::new();
            let log = (graph.nodes as f32).log2() as usize;
            let mut bfs_visited = FastBitvec::new(graph.nodes);

            StandardBFS::new(&self.g_1, node, &mut bfs_visited)
                .enumerate()
                .take_while(|(i, _)| (*i + 1) <= log)
                .map(|(_, n)| n)
                .for_each(|n| {
                    visited.set(n, true);
                    subgraph.push(n);
                });

            //println!("subgraph: {:?}", subgraph.len());

            if subgraph.len() >= log {
                subgraph.iter().for_each(|n| {
                    self.g.neighbors(*n).iter().for_each(|neighbor| {
                        if !subgraph.contains(neighbor) {
                            self.g_1.remove_edge((*n, *neighbor));
                        }
                    })
                });
                subgraph.iter().for_each(|n| self.big.set(*n, true));
            } else {
                subgraph.iter().for_each(|n| self.small.set(*n, true));
            }
        }
        println!("finished cloud part I");
        println!(
            "small: {}",
            self.start.iter_1().filter(|n| self.small.get(*n)).count()
        );
        self.construct_critical_leaf_bridge();
    }
}

#[derive(Debug, Clone)]
pub struct F<'a> {
    f: Graph,
    node_to_cloud: Vec<usize>,
    //TODO: Dieser Vec braucht bedeutend mehr Speicher als theoretisch nötig
    cloud_to_node: Vec<usize>,
    weights: Vec<usize>,
    cloud_part: &'a CloudPartition<'a>,
    simplified: bool,
}

impl<'a> F<'a> {
    fn new_empty(cloud_part: &'a CloudPartition, simplified: bool) -> Self {
        F {
            f: Graph::new(),
            node_to_cloud: Vec::new(),
            cloud_to_node: vec![usize::MAX; cloud_part.g.nodes],
            weights: Vec::new(),
            cloud_part,
            simplified,
        }
    }

    pub fn new(cloud_part: &'a CloudPartition, simplified: bool) -> Self {
        let mut f = Self::new_empty(cloud_part, simplified);
        f.add_big_and_critical();
        //f.add_edges_big_critical();
        //f.add_meta_leaves();
        if !simplified {
            //    f.add_meta_bridges();
        }
        f
    }

    /*pub fn expand(&self, v: usize) -> Subgraph<'a> {
        if self.simplified {
            return match self.cloud_part.r#type(self.node_to_cloud[v]) {
                CloudType::Big | CloudType::Critical | CloudType::Bridge => Subgraph::new(
                    self.cloud_part.g,
                    self.cloud_part.cloud(self.node_to_cloud[v]),
                ),
                CloudType::Leaf => self.expand_leaf(v),
                _ => panic!("something went wrong constructing bridge, leaf and critical"),
            };
        }
        match self.cloud_part.r#type(self.node_to_cloud[v]) {
            CloudType::Big | CloudType::Critical => Subgraph::new(
                self.cloud_part.g,
                self.cloud_part.cloud(self.node_to_cloud[v]),
            ),
            CloudType::Leaf => self.expand_leaf(v),
            CloudType::Bridge => self.expand_bridge(v),
            _ => panic!("something went wrong constructing bridge, leaf and critical"),
        }
    }

    fn expand_leaf(&self, v: usize) -> Subgraph<'a> {
        let mut g_leaf = Subgraph::new(
            self.cloud_part.g,
            self.cloud_part.cloud(self.node_to_cloud[v]),
        );
        let c = self.cloud_part.cloud(
            g_leaf
                .subset
                .iter_1()
                .flat_map(|n| self.cloud_part.g.neighbors(n))
                .find(|n| !g_leaf.subset.get(*n))
                .unwrap(),
        );

        c.iter().for_each(|n| g_leaf.add_to_subgraph(*n));

        self.cloud_part
            .adjacent_clouds(&c, &[CloudType::Leaf])
            .iter()
            .for_each(|neighbor| {
                if g_leaf.subset.get(*neighbor) {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*neighbor);
                c_1.iter().for_each(|n| g_leaf.add_to_subgraph(*n));
            });

        //let mut subset = ChoiceDict::new(self.cloud_part.g.nodes.len());
        let subset = g_leaf
            .subset
            .iter_1()
            .filter(|n| self.cloud_part.r#type(*n) == CloudType::Leaf)
            .collect();

        Subgraph::new(self.cloud_part.g, subset)
    }*/

    /*fn expand_bridge(&self, _v: usize) -> Subgraph<'a> {
        // create f' that contains big nodes and an edge between two nodes when there is a meta bridge connecting these nodes
        //split each edge: adding corresponding meta bridge, direct edges towards direction of original edge
        todo!()
    }*/

    fn add_big_and_critical(&mut self) {
        let mut x = FastBitvec::new(self.cloud_part.g.nodes);
        let mut relevant = FastBitvec::new(self.cloud_part.g.nodes);

        for n in 0..self.cloud_part.g.nodes {
            if self.cloud_part.start.get(n) {
                match self.cloud_part.cloud_type(n) {
                    CloudType::Big | CloudType::Critical => relevant.set(n, true),
                    CloudType::Bridge => {
                        if self.simplified {
                            relevant.set(n, true)
                        }
                    }
                    _ => {}
                }
            }
        }

        relevant.iter_1().for_each(|n| {
            let cloud = self.cloud_part.cloud(n);
            self.f.add_node([].to_vec());
            self.weights.push(cloud.len());
            let v_dash = *cloud.iter().min().unwrap();
            self.node_to_cloud.push(v_dash);
            self.cloud_to_node[v_dash] = self.f.nodes - 1;
            x.set(v_dash, true);
        });
    }

    /*fn add_edges_big_critical(&mut self) {
        let mut completed = FastBitvec::new(self.cloud_part.g.nodes.len());
        let mut discovered = FastBitvec::new(self.cloud_part.g.nodes.len());

        while let Some(v) = completed.clone().iter_0().find(|n| {
            if !self.simplified {
                self.cloud_part.big.get(*n) || self.cloud_part.critical.get(*n)
            } else {
                self.cloud_part.big.get(*n)
                    || self.cloud_part.critical.get(*n)
                    || self.cloud_part.bridge.get(*n)
            }
        }) {
            let cloud = self.cloud_part.cloud(v);
            cloud.iter().for_each(|n| completed.set(*n, true));

            let neighbors = if self.simplified {
                self.cloud_part.adjacent_clouds(
                    &cloud,
                    &[CloudType::Big, CloudType::Critical, CloudType::Bridge],
                )
            } else {
                self.cloud_part
                    .adjacent_clouds(&cloud, &[CloudType::Big, CloudType::Critical])
            };

            neighbors.iter().for_each(|n| {
                if discovered.get(*n) {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*n);
                c_1.iter().for_each(|w| discovered.set(*w, true));
                let w = self.cloud_to_node[c_1.iter().copied().min().unwrap()];
                let v_dash = self.cloud_to_node[cloud.iter().copied().min().unwrap()];
                self.f.add_edge((w, v_dash));
            });

            discovered = FastBitvec::new(self.cloud_part.g.nodes.len());
        }
    }*/

    /*fn add_meta_leaves(&mut self) {
        let mut completed = FastBitvec::new(self.cloud_part.g.nodes.len());
        let mut discovered = FastBitvec::new(self.cloud_part.g.nodes.len());

        while let Some(v) = completed.clone().iter_0().find(|n| {
            self.cloud_part.r#type(*n) == CloudType::Big
                || self.cloud_part.r#type(*n) == CloudType::Critical
        }) {
            let cloud = self.cloud_part.cloud(v);
            cloud.iter().for_each(|n| completed.set(*n, true));

            let neighbors = self.cloud_part.adjacent_clouds(&cloud, &[CloudType::Leaf]);

            neighbors.iter().for_each(|n| {
                if discovered.get(*n) {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*n);
                c_1.iter().for_each(|w| discovered.set(*w, true));
            });

            if discovered.choice_1().is_none() {
                continue;
            }

            let v_1 = discovered.iter_1().min().unwrap();

            self.cloud_to_node[v_1] = self.f.nodes.len() - 1;
            self.node_to_cloud.push(v_1);
            self.f
                .add_node([self.cloud_to_node[cloud.iter().copied().min().unwrap()]].to_vec());
            self.weights.push(discovered.iter_1().count());

            discovered = FastBitvec::new(self.cloud_part.g.nodes.len());
        }
    }

    fn add_meta_bridges(&mut self) {
        //TODO: Nochmal nach Paper implementieren, effizienter und so
        let mut completed = FastBitvec::new(self.cloud_part.g.nodes.len());
        let mut discovered = FastBitvec::new(self.cloud_part.g.nodes.len());

        while let Some(v) = completed
            .clone()
            .iter_0()
            .find(|n| self.cloud_part.big.get(*n) || self.cloud_part.critical.get(*n))
        {
            let cloud = self.cloud_part.cloud(v);
            cloud.iter().for_each(|n| completed.set(*n, true));

            //TODO: construct_gb umschreiben
            //TODO: adjacent_clouds gibts nicht mehr
            let mut g_b = self.construct_g_b(self.cloud_part, &cloud);
            let mut g_a = Subgraph::new(
                self.cloud_part.g,
                self.cloud_part
                    .g
                    .nodes
                    .iter()
                    .enumerate()
                    .map(|(i, _)| i)
                    .collect(),
            );

            //start at an arbitrary bridge cloud in gb
            let b_start = g_b
                .subset
                .iter_1()
                .find(|n| self.cloud_part.r#type(*n) == CloudType::Bridge)
                .unwrap();

            let b = self.cloud_part.cloud(b_start);

            //remove the edges incident to vertices of b and c from gb
            b.subset.iter_1().for_each(|n_b| {
                let neighbors: Vec<usize> = g_b
                    .neighbors(*n_b)
                    .iter()
                    .filter(|neighbor| cloud.subset.get(**neighbor))
                    .copied()
                    .collect();

                for neighbor in neighbors {
                    g_b.remove_edge((*n_b, neighbor))
                }
            });

            //traverse to big cloud c'
            let c_1_start = b
                .iter()
                .flat_map(|n| g_b.neighbors(*n))
                .find(|n| self.cloud_part.r#type(*n) == CloudType::Big)
                .unwrap();

            let c_dash = self.cloud_part.cloud(c_1_start);

            //explore all adjacent bridge clouds
            let mut adjacent_bridge_clouds = Vec::new();

            for node in c_dash.subset.iter_1() {
                if !c_dash.subset.get(*node) {
                    continue;
                }
                g_b.neighbors(*node)
                    .iter()
                    .filter(|n| {
                        !c_dash.subset.get(**n) && self.cloud_part.r#type(**n) == CloudType::Bridge
                    })
                    .for_each(|n| {
                        let c = self.cloud_part.cloud(*n);
                        for neighbor in adjacent_bridge_clouds.clone() {
                            if c.subset.get(neighbor) {
                                return;
                            }
                        }
                        adjacent_bridge_clouds.push(*n);
                    });
            }

            //remove all edges incident to b and c' from ga and gb
            b.subset.iter_1().for_each(|n_b| {
                let neighbors: Vec<usize> = g_a
                    .neighbors(*n_b)
                    .iter()
                    .filter(|neighbor| c_dash.subset.get(**neighbor))
                    .copied()
                    .collect();

                for neighbor in neighbors {
                    g_a.remove_edge((*n_b, neighbor));
                    g_b.remove_edge((*n_b, neighbor))
                }
            });

            let u_1 = self.cloud_to_node[cloud.subset.iter_1().copied().min().unwrap()];
            let v_1 = self.cloud_to_node[c_dash.subset.iter_1().copied().min().unwrap()];
            self.f.add_node([v_1, u_1].to_vec());
            self.weights.push(adjacent_bridge_clouds.len());
            //self.node_to_cloud.push(*w_1);
            //self.cloud_to_node[*w_1] = self.f.nodes.len() - 1;
        }
    }

    fn construct_g_b(&'a self, cloud_part: &'a CloudPartition, cloud: &Subgraph) -> Subgraph<'_> {
        let mut sub = Subgraph::new(cloud_part.g, Vec::new());
        cloud.subset.iter_1().for_each(|n| sub.add_to_subgraph(n));

        let mut clouds = vec![cloud.subset.choice_1().unwrap()];

        while let Some(c) = clouds.pop() {
            let c_cloud = cloud_part.cloud(c);
            let mut neighbors;

            if cloud_part.r#type(c) == CloudType::Bridge {
                neighbors = self.cloud_part.adjacent_clouds(
                    &c_cloud,
                    &[CloudType::Bridge, CloudType::Critical, CloudType::Big],
                );
                neighbors.retain(|n| !sub.subset.get(*n));
            } else {
                neighbors = self
                    .cloud_part
                    .adjacent_clouds(&c_cloud, &[CloudType::Bridge]);
                neighbors.retain(|n| !sub.subset.get(*n));
            }

            for n in neighbors {
                let c_1 = cloud_part.cloud(n);
                c_1.iter().for_each(|n| sub.add_to_subgraph(*n));

                if cloud_part.r#type(c_1[0]) == CloudType::Bridge {
                    clouds.push(c_1[0]);
                }
            }
        }
        sub
    }*/
}

#[cfg(test)]
mod tests {

    use std::{fs::File, io::BufReader};

    use super::*;
    //use crate::tools::graph_visualizer::*;

    #[test]
    pub fn test() {
        /*let graph = crate::data_structures::graph::Graph::new_with_edges(
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
        );*/
        let g = File::open("./tests/planar_embedding1000000.pg").unwrap();
        let buf_read = BufReader::new(g);

        let graph = Graph::try_from(buf_read).unwrap();

        //println!("Graph loaded");
        //let g_dot = dot_graph(&graph, &[]);
        //println!("dot string generated");
        //fs::write("./g.dot", g_dot).unwrap();

        let cloud_part = CloudPartition::new(&graph);
        println!("cloud part generated");
        println!(
            "big: {}",
            cloud_part
                .start
                .iter_1()
                .filter(|n| cloud_part.big.get(*n))
                .count()
        );
        println!(
            "critical: {}",
            cloud_part
                .start
                .iter_1()
                .filter(|i| cloud_part.critical.get(*i))
                .count()
        );
        println!(
            "leaf: {}",
            cloud_part
                .start
                .iter_1()
                .filter(|i| cloud_part.leaf.get(*i))
                .count()
        );
        println!(
            "bridge: {}",
            cloud_part
                .start
                .iter_1()
                .filter(|i| cloud_part.bridge.get(*i))
                .count()
        );

        /*let subgraphs: Vec<Vec<usize>> = cloud_part
            .start
            .iter_1()
            .map(|n| cloud_part.cloud(n))
            .collect();

        let cloud_p_dot = dot_graph(&graph, &subgraphs);
        fs::write("./cloud_part.dot", cloud_p_dot).unwrap();*/
        //let f = F::new(&cloud_part, true);

        /*let mut big_nodes = Vec::new();
        let mut critical_nodes = Vec::new();
        let mut leaf_nodes = Vec::new();
        let mut bridge_nodes = Vec::new();

        f.f.nodes.iter().enumerate().map(|(i, _)| i).for_each(|n| {
            match f.cloud_part.r#type(f.node_to_cloud[n]) {
                CloudType::Big => big_nodes.push(n),
                CloudType::Critical => critical_nodes.push(n),
                CloudType::Leaf => leaf_nodes.push(n),
                CloudType::Bridge => bridge_nodes.push(n),
                _ => panic!("something went wrong constructing leaf, critical and bridge"),
            }
        });

        let subgraphs = &[
            Subgraph::new(&f.f, big_nodes),
            Subgraph::new(&f.f, critical_nodes),
            Subgraph::new(&f.f, leaf_nodes),
            Subgraph::new(&f.f, bridge_nodes),
        ];

        let f_dot = dot_graph(&f.f, subgraphs);
        fs::write("./f.dot", f_dot).unwrap();*/

        /*println!(
            "{:?}",
            f.expand(5)
                .subset
                .iter()
                .enumerate()
                .filter(|(_, n)| *n.as_ref())
                .map(|(i, _)| i)
                .collect::<Vec<usize>>()
        );*/
    }

    /*#[test]
    pub fn test_choice_dict() {
        let mut choice_dict = ChoiceDict::new(1000);
        for i in 0..96 {
            choice_dict.set(i);
        }

        assert_eq!(choice_dict.get(999), 0);
        choice_dict.set(999);
        assert_eq!(choice_dict.get(999), 1);
    }*/
}
