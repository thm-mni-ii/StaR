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

    /**
    Creates a cloud partition from a graph.

    # Example
    ```
    use star::data_structures::graph::Graph;
    use star::algorithms::graph_coarsening::CloudPartition;
    use star::algorithms::graph_coarsening::F;

    let mut graph = Graph::new_with_edges(
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

    let cloud_part = CloudPartition::new(&graph);
    ```
     */
    pub fn new(graph: &'b Graph) -> Self {
        let mut cloud_part = Self::new_empty(graph);
        cloud_part.cloud_partition(graph, &mut FastBitvec::new(graph.nodes));

        cloud_part
    }

    /**
    Returns the Type of a the cloud node v is a part of.

    # Example
    ```
    use star::data_structures::graph::Graph;
    use star::algorithms::graph_coarsening::CloudPartition;
    use star::algorithms::graph_coarsening::F;
    use star::algorithms::graph_coarsening::CloudType;

    let mut graph = Graph::new_with_edges(
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

    let cloud_part = CloudPartition::new(&graph);
    assert_eq!(cloud_part.cloud_type(0), CloudType::Big);
    ```
     */
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

    /**
    Returns all nodes in the cloud of v. Additionally expects a FastBitvec used internally for the BFS.

    # Example
    ```
    use star::data_structures::graph::Graph;
    use star::algorithms::graph_coarsening::CloudPartition;
    use star::algorithms::graph_coarsening::F;

    let mut graph = Graph::new_with_edges(
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

    let cloud_part = CloudPartition::new(&graph);
    assert_eq!(cloud_part.cloud(0), vec![0, 1, 6, 2]);
    ```
     */
    pub fn cloud(&self, v: usize) -> Vec<usize> {
        self.cloud_with_bitvec(v, &mut FastBitvec::new(self.g.nodes))
    }

    fn cloud_with_bitvec(&self, v: usize, visited: &mut FastBitvec) -> Vec<usize> {
        StandardBFS::new(&self.g_1, v, visited).collect()
    }

    /**
    Returns wether the edge (v, u) is an edge connecting two clouds, making it a border edge.
    # Example
    ```
    use star::data_structures::graph::Graph;
    use star::algorithms::graph_coarsening::CloudPartition;
    use star::algorithms::graph_coarsening::F;

    let mut graph = Graph::new_with_edges(
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

    let cloud_part = CloudPartition::new(&graph);
    assert_eq!(cloud_part.border(6, 7), true);
    ```
     */
    pub fn border(&self, v: usize, u: usize) -> bool {
        !self.g_1.neighbors(v).contains(&u)
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
        let mut bitvec_for_small = FastBitvec::new(self.g.nodes);
        let cloud = self.cloud_with_bitvec(n, &mut bitvec_for_small);

        for node in cloud.clone() {
            visited_big_clouds.set(node, true);
        }
        for node in cloud {
            for edge in self.g.neighbors(node).iter().enumerate() {
                if irrelevant_edges[node].get(edge.0) {
                    continue;
                }
                if self.small.get(*edge.1) {
                    self.visit_small_cloud(
                        irrelevant_edges,
                        visited_big_clouds,
                        &mut bitvec_for_small,
                        *edge.1,
                    );
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
        visited: &mut FastBitvec,
        n: usize,
    ) {
        for node in self.cloud_with_bitvec(n, visited) {
            if self.critical.get(node) {
                continue;
            }
            self.increase_node_level(node);
            for edge in self.g.neighbors(node).iter().enumerate() {
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
        let log = (graph.nodes as f32).log2() as usize;
        while let Some(node) = visited.choice_0() {
            if graph.deleted.get(node) {
                visited.set(node, true);
                continue;
            }
            self.start.set(node, true);
            let mut subgraph = Vec::new();
            let mut bfs_visited = FastBitvec::new(graph.nodes);

            StandardBFS::new(&self.g_1, node, &mut bfs_visited)
                .enumerate()
                .take_while(|(i, _)| (*i + 1) <= log)
                .map(|(_, n)| n)
                .for_each(|n| {
                    visited.set(n, true);
                    subgraph.push(n);
                });

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
}

impl<'a> F<'a> {
    fn new_empty(cloud_part: &'a CloudPartition) -> Self {
        F {
            f: Graph::new(),
            node_to_cloud: Vec::new(),
            cloud_to_node: vec![usize::MAX; cloud_part.g.nodes],
            weights: Vec::new(),
            cloud_part,
        }
    }

    /**
    Creates a coarsened graph from a cloud partition.

    # Example
    ```
    use star::data_structures::graph::Graph;
    use star::algorithms::graph_coarsening::CloudPartition;
    use star::algorithms::graph_coarsening::F;

    let mut graph = Graph::new_with_edges(
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

    let cloud_part = CloudPartition::new(&graph);
    let f = F::new(&cloud_part);
    ```
    */
    pub fn new(cloud_part: &'a CloudPartition) -> Self {
        let mut f = Self::new_empty(cloud_part);
        f.add_big_and_critical();
        f.add_edges_big_critical();
        f
    }

    /**
    Returns all nodes in the original graph represented by a node in the coarsened graph.

    # Example
    ```
    use star::data_structures::graph::Graph;
    use star::algorithms::graph_coarsening::CloudPartition;
    use star::algorithms::graph_coarsening::F;

    let mut graph = Graph::new_with_edges(
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

    let cloud_part = CloudPartition::new(&graph);
    let f = F::new(&cloud_part);
    let cloud_represented_by_node_5 = f.expand(5);
    ```
    */
    pub fn expand(&self, v: usize) -> Vec<usize> {
        self.cloud_part.cloud_with_bitvec(
            self.node_to_cloud[v],
            &mut FastBitvec::new(self.cloud_part.g.nodes),
        )
    }

    fn add_big_and_critical(&mut self) {
        let mut cloud_bitvec = FastBitvec::new(self.cloud_part.g.nodes);

        self.cloud_part.start.iter_1().for_each(|n| {
            let cloud = self.cloud_part.cloud_with_bitvec(n, &mut cloud_bitvec);
            self.f.add_node([].to_vec());
            self.weights.push(cloud.len());
            let v_dash = *cloud.iter().min().unwrap();
            self.node_to_cloud.push(v_dash);
            self.cloud_to_node[v_dash] = self.f.nodes - 1;
        });
    }

    fn add_edges_big_critical(&mut self) {
        let mut completed = FastBitvec::new(self.cloud_part.g.nodes);
        let mut discovered = FastBitvec::new(self.cloud_part.g.nodes);
        let mut cloud_bitvec = FastBitvec::new(self.cloud_part.g.nodes);

        while let Some(v) = completed.choice_0() {
            let cloud = self.cloud_part.cloud_with_bitvec(v, &mut cloud_bitvec);
            cloud.iter().for_each(|n| completed.set(*n, true));
            for n in cloud.iter() {
                for neighbor in self.cloud_part.g.neighbors(*n) {
                    if !discovered.get(*neighbor) && self.cloud_part.border(*n, *neighbor) {
                        let c_dash = self.cloud_part.cloud_with_bitvec(
                            *neighbor,
                            &mut FastBitvec::new(self.cloud_part.g.nodes),
                        );

                        c_dash.iter().for_each(|n| discovered.set(*n, true));

                        let v = c_dash.iter().min().unwrap();
                        let u = cloud.iter().min().unwrap();

                        self.f
                            .add_edge((self.cloud_to_node[*v], self.cloud_to_node[*u]));
                    }
                }
                discovered.bitvec.fill(false);
            }
        }
    }
}

/*#[cfg(test)]
mod tests {

    use std::{
        fs::{self, File, OpenOptions},
        io::{BufReader, Write},
    };

    use cpu_time::ProcessTime;
    use rand::Rng;

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
        let g = File::open("./tests/graphs/planar_embedding1000000.pg").unwrap();
        let buf_read = BufReader::new(g);

        let graph = Graph::try_from(buf_read).unwrap();
        //delete_arbitrary_amount_of_edges(&mut graph);

        //println!("Graph loaded");
        //let g_dot = dot_graph(&graph, &[]);
        //println!("dot string generated");
        //fs::write("./g.dot", g_dot).unwrap();
        println!("start cloud part");

        let start = ProcessTime::now();
        let cloud_part = CloudPartition::new(&graph);
        let end = start.elapsed();

        println!("cloud part generated, took {:?}", end);
        println!(
            "big: {}",
            cloud_part
                .start
                .iter_1()
                .filter(|n| cloud_part.big.get(*n))
                .count()
        );
        println!(
            "small: {}",
            cloud_part
                .start
                .iter_1()
                .filter(|n| cloud_part.small.get(*n))
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

        println!(
            "{}",
            StandardBFS::new(&graph, 0, &mut FastBitvec::new(graph.nodes)).count()
        );
        println!(
            "{}",
            cloud_part
                .small
                .iter_1()
                .filter(|n| !cloud_part.critical.get(*n)
                    && !cloud_part.bridge.get(*n)
                    && !cloud_part.leaf.get(*n))
                .count()
        );

        /*let subgraphs: Vec<Vec<usize>> = cloud_part
            .start
            .iter_1()
            .map(|n| cloud_part.cloud(n, &mut FastBitvec::new(graph.nodes)))
            .collect();

        let cloud_p_dot = dot_graph(&graph, &subgraphs);
        let g_dash_dot = dot_graph(&cloud_part.g_1, &[]);
        fs::write("./g_dash.dot", g_dash_dot).unwrap();
        fs::write("./cloud_part.dot", cloud_p_dot).unwrap();*/
        let f = F::new(&cloud_part);

        //let f_dot = dot_graph(&f.f, &[]);
        //fs::write("./f.dot", f_dot).unwrap();

        println!("{:?}", f.expand(666));
    }

    #[test]
    fn test_all() {
        fs::write(
            "./results.csv",
            "nodes;edges;Verhältnis Knoten-Kanten;time;big;small;small bereinigt;critical;bridge;leaf;Verhältnis big-small;Anteil Critical;Anteil Bridge;Anteil Leaf",
        )
        .unwrap();

        for file in fs::read_dir("./tests/graphs").expect("no such directory") {
            let f = File::open(format!(
                "./tests/graphs/{}",
                file.unwrap().file_name().to_str().unwrap()
            ))
            .expect("file not found");
            let buf_read = BufReader::new(f);
            let mut graph = Graph::try_from(buf_read).unwrap();
            if graph.nodes == 5_000_000 {
                delete_arbitrary_amount_of_edges(&mut graph);
            }
            find_largest_connected_component(&mut graph);

            let num_edges = graph.edges.iter().map(|n| n.len()).sum::<usize>() / 2;

            let start = ProcessTime::now();
            let cloud_part = CloudPartition::new(&graph);
            let end = start.elapsed();

            let big = cloud_part
                .start
                .iter_1()
                .filter(|n| cloud_part.big.get(*n))
                .count();

            let critical = cloud_part
                .start
                .iter_1()
                .filter(|i| cloud_part.critical.get(*i))
                .count();

            let bridge = cloud_part
                .start
                .iter_1()
                .filter(|i| cloud_part.bridge.get(*i))
                .count();

            let leaf = cloud_part
                .start
                .iter_1()
                .filter(|i| cloud_part.leaf.get(*i))
                .count();

            let small = cloud_part
                .start
                .iter_1()
                .filter(|i| cloud_part.small.get(*i))
                .count();

            let mut res = OpenOptions::new()
                .write(true)
                .append(true)
                .open("./results.csv")
                .unwrap();

            res.write_all(
                format!(
                    "\n{};{};{};{:?};{};{};{};{};{};{};{};{};{};{}",
                    graph.nodes - graph.deleted.iter_1().count(),
                    num_edges,
                    num_edges as f32 / graph.nodes as f32,
                    end,
                    big,
                    small,
                    critical + bridge + leaf,
                    critical,
                    bridge,
                    leaf,
                    big as f32 / (critical + bridge + leaf) as f32,
                    critical as f32 / (critical + bridge + leaf) as f32,
                    bridge as f32 / (critical + bridge + leaf) as f32,
                    leaf as f32 / (critical + bridge + leaf) as f32,
                )
                .as_bytes(),
            )
            .expect("write failed");
        }
    }

    fn delete_arbitrary_amount_of_edges(g: &mut Graph) {
        let n = rand::thread_rng().gen_range(0..10_000_000);
        println!("n: {}", n);
        for _ in 0..n {
            let u = rand::thread_rng().gen_range(0..g.nodes);
            if g.edges[u].is_empty() {
                continue;
            }
            let v = rand::thread_rng().gen_range(0..g.edges[u].len());
            g.remove_edge((u, g.edges[u][v]));
        }

        for n in 0..g.nodes {
            if g.edges[n].is_empty() {
                g.remove_node(n)
            }
        }
    }

    fn find_largest_connected_component(g: &mut Graph) {
        let mut visited = FastBitvec::new(g.nodes);
        let mut largest = 0_usize;
        let mut index_largest = 0_usize;
        let mut largest_component = FastBitvec::new(g.nodes);

        while let Some(n) = visited.choice_0() {
            if g.deleted.get(n) {
                visited.set(n, true);
                continue;
            }
            let mut bfs_visited = FastBitvec::new(g.nodes);
            let len = StandardBFS::new(g, n, &mut bfs_visited)
                .map(|v| {
                    visited.set(v, true);
                    v
                })
                .count();

            if len > largest {
                largest = len;
                index_largest = n;
            }
        }

        StandardBFS::new(g, index_largest, &mut FastBitvec::new(g.nodes))
            .for_each(|n| largest_component.set(n, true));

        for i in 0..g.nodes {
            if !largest_component.get(i) && !g.deleted.get(i) {
                g.remove_node(i);
            }
        }
    }
}*/
