use crate::data_structures::graph::Graph;
use crate::data_structures::subgraph::Subgraph;
use bitvec::prelude::*;
//use bitvec::prelude::*;

use super::bfs::{GraphLike, StandardBFS};

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
    start: BitVec,
    big: BitVec,
    small: BitVec,
    leaf: BitVec,
    bridge: BitVec,
    critical: BitVec,
    g_1: Subgraph<'a>,
    g: &'a Graph,
}

impl<'b> CloudPartition<'b> {
    fn new_empty(graph: &'b Graph) -> Self {
        let subset = (0..graph.nodes.len()).collect();
        CloudPartition {
            start: bitvec![0; graph.nodes.len()],
            big: bitvec![0; graph.nodes.len()],
            small: bitvec![0; graph.nodes.len()],
            leaf: bitvec![0; graph.nodes.len()],
            bridge: bitvec![0; graph.nodes.len()],
            critical: bitvec![0; graph.nodes.len()],
            g_1: Subgraph::new(graph, subset),
            g: graph,
        }
    }

    pub fn new(graph: &'b Graph) -> Self {
        let mut cloud_part = Self::new_empty(graph);
        cloud_part.cloud_partition(graph, &mut bitvec![0; graph.nodes.len()]);

        cloud_part
    }

    pub fn r#type(&self, v: usize) -> CloudType {
        if self.big.get(v).as_deref() == Some(&true) {
            return CloudType::Big;
        }
        if self.leaf.get(v).as_deref() == Some(&true) {
            return CloudType::Leaf;
        }
        if self.bridge.get(v).as_deref() == Some(&true) {
            return CloudType::Bridge;
        }
        if self.critical.get(v).as_deref() == Some(&true) {
            return CloudType::Critical;
        }
        if self.small.get(v).as_deref() == Some(&true) {
            return CloudType::Small;
        }
        panic!("something went wrong constructing leaf, critical and bridge")
    }

    pub fn cloud(&self, v: usize) -> Subgraph {
        let subset = StandardBFS::new(&self.g_1, v).collect();
        Subgraph::new(self.g, subset)
    }

    pub fn border(&self, v: usize, u: usize) -> bool {
        self.g_1.neighbors(v).contains(&u)
    }

    fn adjacent_clouds(&self, subgraph: &Subgraph<'_>, c_type: Vec<CloudType>) -> Vec<usize> {
        let mut neighbors = Vec::new();
        for node in subgraph.subset.iter().enumerate() {
            if !node.1.as_ref() {
                continue;
            }
            self.g
                .neighbors(node.0)
                .iter()
                .filter(|n| {
                    subgraph.subset.get(**n).as_deref() != Some(&true)
                        && c_type.contains(&self.r#type(**n))
                })
                .for_each(|n| {
                    let c = self.cloud(*n);
                    for neighbor in neighbors.clone() {
                        if c.subset.get(neighbor).as_deref() == Some(&true) {
                            return;
                        }
                    }
                    neighbors.push(*n);
                })
        }
        neighbors
    }

    fn _construct_critical_leaf_bridge(&mut self) {
        let mut leaf = bitvec![0; self.g.nodes.len()];
        let mut bridge = bitvec![0; self.g.nodes.len()];
        let mut critical = bitvec![0; self.g.nodes.len()];
        for n in self
            .start
            .iter()
            .enumerate()
            .filter(|(i, n)| *n.as_ref() && self.big.get(*i).as_deref() == Some(&true))
            .map(|(i, _)| i)
        {
            let cloud = self.cloud(n);
            println!("{:?}", n);

            for neighbor in self.adjacent_clouds(&cloud, vec![CloudType::Small]) {
                if self.critical.get(neighbor).as_deref() == Some(&true) {
                    continue;
                }
                let c = self.cloud(neighbor);

                for node in c
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                {
                    if leaf.get(node).as_deref() == Some(&false)
                        && bridge.get(node).as_deref() == Some(&false)
                    {
                        leaf.set(node, true);
                    } else if leaf.get(node).as_deref() == Some(&true) {
                        leaf.set(node, false);
                        bridge.set(node, true);
                    } else if bridge.get(node).as_deref() == Some(&true) {
                        bridge.set(node, false);
                        critical.set(node, true);
                    }
                }
            }
        }
        self.leaf = leaf;
        self.bridge = bridge;
        self.critical = critical;
    }

    fn construct_critical_leaf_bridge_alt(&mut self) {
        //let small_clouds = Vec::new();

        let small_clouds = self
            .start
            .iter()
            .enumerate()
            .filter(|(i, n)| *n.as_ref() && self.small.get(*i).as_deref() == Some(&true))
            .map(|(i, _)| i);

        for n in small_clouds {
            println!("{}", n);
            let cloud = self.cloud(n);
            //let cloud = Subgraph::new(self.g, vec![1, 15, 39, 54, 4, 10, 14, 350, 500, 43]);
            let adjacent_clouds = self.adjacent_clouds(&cloud, vec![CloudType::Big]).len();

            if adjacent_clouds == 1 {
                cloud
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| *v.as_ref())
                    .map(|(i, _)| i)
                    .for_each(|n| {
                        self.leaf.set(n, true);
                    });
            } else if adjacent_clouds == 2 {
                cloud
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| *v.as_ref())
                    .map(|(i, _)| i)
                    .for_each(|n| {
                        self.bridge.set(n, true);
                    });
            } else {
                cloud
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, v)| *v.as_ref())
                    .map(|(i, _)| i)
                    .for_each(|n| {
                        self.leaf.set(n, true);
                    });
            }
        }
    }

    fn cloud_partition<'a>(&mut self, graph: &'a Graph, visited: &'a mut BitVec) {
        while let Some(node) = visited
            .iter()
            .enumerate()
            .find(|(_, n)| !*n.as_ref())
            .map(|(i, _)| i)
        {
            //println!("node: {}", node);
            self.start.set(node, true);
            let mut subgraph = Vec::new();

            StandardBFS::new(&self.g_1, node)
                .enumerate()
                .take_while(|(i, _)| ((*i + 1) as f32) <= (graph.nodes.len() as f32).log2())
                .map(|(_, n)| n)
                .for_each(|n| {
                    visited.set(n, true);
                    subgraph.push(n);
                });

            //println!("subgraph: {:?}", subgraph.len());

            if subgraph.len() >= (graph.nodes.len() as f32).log2() as usize {
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
        self.construct_critical_leaf_bridge_alt();
    }
}

#[derive(Debug)]
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
            cloud_to_node: vec![usize::MAX; cloud_part.g.nodes.len()],
            weights: Vec::new(),
            cloud_part,
            simplified,
        }
    }

    pub fn new(cloud_part: &'a CloudPartition, simplified: bool) -> Self {
        let mut f = Self::new_empty(cloud_part, simplified);
        f.add_big_and_critical();
        f.add_edges_big_critical();
        f.add_meta_leaves();
        if !simplified {
            f.add_meta_bridges();
        }
        f
    }

    pub fn expand(&self, v: usize) -> Subgraph<'a> {
        if self.simplified {
            return match self.cloud_part.r#type(self.node_to_cloud[v]) {
                CloudType::Big | CloudType::Critical | CloudType::Bridge => {
                    self.cloud_part.cloud(self.node_to_cloud[v])
                }
                CloudType::Leaf => self.expand_leaf(v),
                _ => panic!("something went wrong constructing bridge, leaf and critical"),
            };
        }
        match self.cloud_part.r#type(self.node_to_cloud[v]) {
            CloudType::Big | CloudType::Critical => self.cloud_part.cloud(self.node_to_cloud[v]),
            CloudType::Leaf => self.expand_leaf(v),
            CloudType::Bridge => self.expand_bridge(v),
            _ => panic!("something went wrong constructing bridge, leaf and critical"),
        }
    }

    fn expand_leaf(&self, v: usize) -> Subgraph<'a> {
        let mut g_leaf = self.cloud_part.cloud(self.node_to_cloud[v]);
        let c = self.cloud_part.cloud(
            g_leaf
                .subset
                .iter()
                .enumerate()
                .filter(|(_, n)| *n.as_ref())
                .map(|(i, _)| i)
                .flat_map(|n| self.cloud_part.g.neighbors(n))
                .find(|n| g_leaf.subset.get(*n).as_deref() == Some(&false))
                .unwrap(),
        );

        c.subset
            .iter()
            .enumerate()
            .filter(|(_, n)| *n.as_ref())
            .map(|(i, _)| i)
            .for_each(|n| g_leaf.add_to_subgraph(n));

        self.cloud_part
            .adjacent_clouds(&c, vec![CloudType::Leaf])
            .iter()
            .for_each(|neighbor| {
                if g_leaf.subset.get(*neighbor).as_deref() == Some(&true) {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*neighbor);
                c_1.subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .for_each(|n| g_leaf.add_to_subgraph(n));
            });

        //let mut subset = ChoiceDict::new(self.cloud_part.g.nodes.len());
        let subset = g_leaf
            .subset
            .iter()
            .enumerate()
            .filter(|(_, n)| *n.as_ref())
            .map(|(i, _)| i)
            .filter(|n| self.cloud_part.r#type(*n) == CloudType::Leaf)
            .collect();

        Subgraph::new(self.cloud_part.g, subset)
    }

    fn expand_bridge(&self, _v: usize) -> Subgraph<'a> {
        // create f' that contains big nodes and an edge between two nodes when there is a meta bridge connecting these nodes
        //split each edge: adding corresponding meta bridge, direct edges towards direction of original edge
        todo!()
    }

    fn add_big_and_critical(&mut self) {
        let mut x = bitvec![0; self.cloud_part.g.nodes.len()];
        let mut visited = bitvec![0; self.cloud_part.g.nodes.len()];
        let mut big_clouds: Vec<usize> = self
            .cloud_part
            .big
            .iter()
            .enumerate()
            .filter(|(_, n)| *n.as_ref())
            .map(|(i, _)| i)
            .collect();
        let mut critical_clouds: Vec<usize> = self
            .cloud_part
            .critical
            .iter()
            .enumerate()
            .filter(|(_, n)| *n.as_ref())
            .map(|(i, _)| i)
            .collect();
        let mut bridge_clouds: Vec<usize> = self
            .cloud_part
            .bridge
            .iter()
            .enumerate()
            .filter(|(_, n)| *n.as_ref())
            .map(|(i, _)| i)
            .collect();

        while if !self.simplified {
            !big_clouds.is_empty() || !critical_clouds.is_empty()
        } else {
            !big_clouds.is_empty() || !critical_clouds.is_empty() || !bridge_clouds.is_empty()
        } {
            let v = if !big_clouds.is_empty() {
                big_clouds[0]
            } else if !critical_clouds.is_empty() {
                critical_clouds[0]
            } else {
                bridge_clouds[0]
            };
            let cloud = self.cloud_part.cloud(v);
            cloud
                .subset
                .iter()
                .enumerate()
                .filter(|(_, n)| *n.as_ref())
                .map(|(i, _)| i)
                .for_each(|n| visited.set(n, true));
            if self.cloud_part.r#type(v) == CloudType::Big {
                big_clouds = self
                    .cloud_part
                    .big
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .filter(|n| visited.get(*n).as_deref() == Some(&false))
                    .collect();
            }
            if self.cloud_part.r#type(v) == CloudType::Critical {
                critical_clouds = self
                    .cloud_part
                    .big
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .filter(|n| visited.get(*n).as_deref() == Some(&false))
                    .collect();
            }
            if self.cloud_part.r#type(v) == CloudType::Bridge {
                bridge_clouds = self
                    .cloud_part
                    .bridge
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .filter(|n| visited.get(*n).as_deref() == Some(&false))
                    .collect();
            }

            self.f.add_node([].to_vec());
            self.weights.push(
                cloud
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .count(),
            );
            self.node_to_cloud.push(v);
            self.cloud_to_node[v] = self.f.nodes.len() - 1;
            x.set(v, true);
        }
    }

    pub fn add_edges_big_critical(&mut self) {
        let mut completed = bitvec![0; self.cloud_part.g.nodes.len()];
        let mut discovered = bitvec![0; self.cloud_part.g.nodes.len()];

        while let Some(v) = completed
            .iter()
            .enumerate()
            .filter(|(_, n)| !*n.as_ref())
            .map(|(i, _)| i)
            .find(|n| {
                if !self.simplified {
                    self.cloud_part.big.get(*n).as_deref() == Some(&true)
                        || self.cloud_part.critical.get(*n).as_deref() == Some(&true)
                } else {
                    self.cloud_part.big.get(*n).as_deref() == Some(&true)
                        || self.cloud_part.critical.get(*n).as_deref() == Some(&true)
                        || self.cloud_part.bridge.get(*n).as_deref() == Some(&true)
                }
            })
        {
            let cloud = self.cloud_part.cloud(v);
            cloud
                .subset
                .iter()
                .enumerate()
                .filter(|(_, n)| *n.as_ref())
                .map(|(i, _)| i)
                .for_each(|n| completed.set(n, true));

            let neighbors = if self.simplified {
                self.cloud_part.adjacent_clouds(
                    &cloud,
                    vec![CloudType::Big, CloudType::Critical, CloudType::Bridge],
                )
            } else {
                self.cloud_part
                    .adjacent_clouds(&cloud, vec![CloudType::Big, CloudType::Critical])
            };

            neighbors.iter().for_each(|n| {
                if discovered.get(*n).as_deref() == Some(&true) {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*n);
                c_1.subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .for_each(|w| discovered.set(w, true));
                let w = self.cloud_to_node[c_1
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .min()
                    .unwrap()];
                self.f.add_edge((w, self.cloud_to_node[v]));
            });

            discovered.fill(false);
        }
    }

    pub fn add_meta_leaves(&mut self) {
        let mut completed = bitvec![0; self.cloud_part.g.nodes.len()];
        let mut discovered = bitvec![0; self.cloud_part.g.nodes.len()];

        while let Some(v) = completed
            .iter()
            .enumerate()
            .filter(|(_, n)| !*n.as_ref())
            .map(|(i, _)| i)
            .find(|n| {
                self.cloud_part.r#type(*n) == CloudType::Big
                    || self.cloud_part.r#type(*n) == CloudType::Critical
            })
        {
            let cloud = self.cloud_part.cloud(v);
            cloud
                .subset
                .iter()
                .enumerate()
                .filter(|(_, n)| *n.as_ref())
                .map(|(i, _)| i)
                .for_each(|n| completed.set(n, true));

            let neighbors = self
                .cloud_part
                .adjacent_clouds(&cloud, vec![CloudType::Leaf]);

            neighbors.iter().for_each(|n| {
                if discovered.get(*n).as_deref() == Some(&true) {
                    return;
                }
                let c_1 = self.cloud_part.cloud(*n);
                c_1.subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .for_each(|w| discovered.set(w, true));
            });

            if discovered
                .iter()
                .enumerate()
                .filter(|(_, n)| *n.as_ref())
                .map(|(i, _)| i)
                .next()
                .is_none()
            {
                continue;
            }

            let v_1 = discovered
                .iter()
                .enumerate()
                .filter(|(_, n)| *n.as_ref())
                .map(|(i, _)| i)
                .min()
                .unwrap();

            self.cloud_to_node[v_1] = self.f.nodes.len() - 1;
            self.node_to_cloud.push(v_1);
            self.f.add_node(
                [self.cloud_to_node[cloud
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .min()
                    .unwrap()]]
                .to_vec(),
            );
            self.weights.push(
                discovered
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .count(),
            );

            discovered.fill(false);
        }
    }

    pub fn add_meta_bridges(&mut self) {
        //TODO: Nochmal nach Paper implementieren, effizienter und so
        let mut completed = bitvec![0; self.cloud_part.g.nodes.len()];
        let mut discovered = bitvec![0; self.cloud_part.g.nodes.len()];
        //let mut _g_a = cloud_part.g.clone();

        while let Some(v) = completed
            .iter()
            .enumerate()
            .filter(|(_, n)| !*n.as_ref())
            .map(|(i, _)| i)
            .find(|n| {
                self.cloud_part.big.get(*n).as_deref() == Some(&true)
                    || self.cloud_part.critical.get(*n).as_deref() == Some(&true)
            })
        {
            let cloud = self.cloud_part.cloud(v);
            cloud
                .subset
                .iter()
                .enumerate()
                .filter(|(_, n)| *n.as_ref())
                .map(|(i, _)| i)
                .for_each(|n| completed.set(n, true));

            let mut g_b = self.construct_g_b(self.cloud_part, &cloud);

            while let Some(b_1) = discovered
                .iter()
                .enumerate()
                .filter(|(_, n)| !*n.as_ref())
                .map(|(i, _)| i)
                .find(|n| g_b.nodes[*n] == 0 && self.cloud_part.r#type(*n) == CloudType::Bridge)
            {
                let b = self.cloud_part.cloud(b_1);
                //remove all edges incident to b AND c
                b.subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .for_each(|n_b| {
                        let neighbors: Vec<usize> = g_b
                            .neighbors(n_b)
                            .iter()
                            .filter(|neighbor| {
                                cloud.subset.get(**neighbor).as_deref() == Some(&true)
                            })
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
                            && cloud.subset.get(*n).as_deref() == Some(&false)
                            && b.subset.get(*n).as_deref() == Some(&false)
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
                    .flat_map(|s: &Subgraph| {
                        s.subset
                            .iter()
                            .enumerate()
                            .filter(|(_, n)| *n.as_ref())
                            .map(|(i, _)| i)
                    })
                    .min()
                    .unwrap();

                for bridge in adjacent_bridge_clouds {
                    for node in bridge
                        .subset
                        .iter()
                        .enumerate()
                        .filter(|(_, n)| *n.as_ref())
                        .map(|(i, _)| i)
                    {
                        discovered.set(node, true)
                    }
                    weight += bridge
                        .subset
                        .iter()
                        .enumerate()
                        .filter(|(_, n)| *n.as_ref())
                        .count();
                }
                //ab hier wieder nach Paper

                let u_1 = self.cloud_to_node[cloud
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .min()
                    .unwrap()];
                let v_1 = self.cloud_to_node[c_dash
                    .subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .min()
                    .unwrap()];
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
        let mut sub = Subgraph::new(cloud_part.g, Vec::new());
        cloud
            .subset
            .iter()
            .enumerate()
            .filter(|(_, n)| *n.as_ref())
            .map(|(i, _)| i)
            .for_each(|n| sub.add_to_subgraph(n));

        let mut clouds = vec![cloud
            .subset
            .iter()
            .enumerate()
            .filter(|(_, n)| *n.as_ref())
            .map(|(i, _)| i)
            .next()
            .unwrap()];

        while let Some(c) = clouds.pop() {
            let c_cloud = cloud_part.cloud(c);
            let mut neighbors;

            if cloud_part.r#type(c) == CloudType::Bridge {
                neighbors = self.cloud_part.adjacent_clouds(
                    &c_cloud,
                    vec![CloudType::Bridge, CloudType::Critical, CloudType::Big],
                );
                neighbors.retain(|n| sub.subset.get(*n).as_deref() == Some(&false));
            } else {
                neighbors = self
                    .cloud_part
                    .adjacent_clouds(&c_cloud, vec![CloudType::Bridge]);
                neighbors.retain(|n| sub.subset.get(*n).as_deref() == Some(&false));
            }

            for n in neighbors {
                let c_1 = cloud_part.cloud(n);
                c_1.subset
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| *n.as_ref())
                    .map(|(i, _)| i)
                    .for_each(|n| sub.add_to_subgraph(n));

                if cloud_part.r#type(
                    c_1.subset
                        .iter()
                        .enumerate()
                        .filter(|(_, n)| *n.as_ref())
                        .map(|(i, _)| i)
                        .next()
                        .unwrap(),
                ) == CloudType::Bridge
                {
                    clouds.push(
                        c_1.subset
                            .iter()
                            .enumerate()
                            .filter(|(_, n)| *n.as_ref())
                            .map(|(i, _)| i)
                            .next()
                            .unwrap(),
                    );
                }
            }
        }

        let mut g_b = cloud_part.g.clone();

        for n in 0..g_b.nodes.len() {
            if sub.subset.get(n).as_deref() == Some(&false) {
                g_b.remove_node(n);
            }
        }
        g_b
    }
}

#[cfg(test)]
mod tests {

    use std::{
        fs::{self, File},
        io::BufReader,
    };

    use crate::tools::graph_visualizer::dot_graph;

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

        println!("Graph loaded");
        //let g_dot = dot_graph(&graph, &[]);
        //println!("dot string generated");
        //fs::write("./g.dot", g_dot).unwrap();

        let cloud_part = CloudPartition::new(&graph);
        println!("cloud part generated");
        println!(
            "big: {}",
            cloud_part
                .big
                .iter()
                .enumerate()
                .filter(|(i, n)| *n.as_ref() && cloud_part.start.get(*i).as_deref() == Some(&true))
                .count()
        );
        println!(
            "critical: {}",
            cloud_part
                .critical
                .iter()
                .enumerate()
                .filter(|(i, n)| *n.as_ref() && cloud_part.start.get(*i).as_deref() == Some(&true))
                .count()
        );
        println!(
            "leaf: {}",
            cloud_part
                .leaf
                .iter()
                .enumerate()
                .filter(|(i, n)| *n.as_ref() && cloud_part.start.get(*i).as_deref() == Some(&true))
                .count()
        );
        println!(
            "bridge: {}",
            cloud_part
                .bridge
                .iter()
                .enumerate()
                .filter(|(i, n)| *n.as_ref() && cloud_part.start.get(*i).as_deref() == Some(&true))
                .count()
        );
        /*let subgraphs: Vec<Subgraph> = cloud_part
        .start
        .iter()
        .enumerate()
        .filter(|(_, n)| *n.as_ref())
        .map(|(i, _)| i)
        .map(|n| cloud_part.cloud(n))
        .collect();*/

        //let cloud_p_dot = dot_graph(&graph, &subgraphs);
        //fs::write("./cloud_part.dot", cloud_p_dot).unwrap();

        //let f = F::new(&cloud_part, true);
        //let f_dot = dot_graph(&f.f, &[]);
        //fs::write("./f.dot", f_dot).unwrap();
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
