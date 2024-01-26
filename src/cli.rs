use std::{
    fs::{self, File},
    io::{BufReader, Error},
};

use clap::{arg, Command};
use cpu_time::ProcessTime;
use star::{
    algorithms::graph_coarsening::{CloudPartition, CloudType, GraphCoarsening},
    data_structures::graph::Graph,
    tools::graph_visualizer::dot_graph,
};

fn main() {
    let cli = load_program_data().get_matches();

    match read_graph(cli.get_one::<String>("file").unwrap()) {
        Err(e) => println!("Error: {}", e),
        Ok(graph) => {
            let start_cp = ProcessTime::now();
            let cloud_partition = CloudPartition::new(&graph);
            let end_cp = start_cp.elapsed();

            println!("Cloud Partition finished, took {:?}", end_cp);
            println!(
                "Number of clouds: {}",
                cloud_partition.start.iter_1().count()
            );
            println!(
                "Big clouds: {}",
                cloud_partition
                    .start
                    .iter_1()
                    .filter(|n| cloud_partition.cloud_type(*n) == CloudType::Big)
                    .count()
            );
            println!(
                "Small clouds: {}",
                cloud_partition
                    .start
                    .iter_1()
                    .filter(|n| cloud_partition.cloud_type(*n) != CloudType::Big)
                    .count()
            );
            println!(
                "Critical clouds: {}",
                cloud_partition
                    .start
                    .iter_1()
                    .filter(|n| cloud_partition.cloud_type(*n) == CloudType::Critical)
                    .count()
            );
            println!(
                "Bridge clouds: {}",
                cloud_partition
                    .start
                    .iter_1()
                    .filter(|n| cloud_partition.cloud_type(*n) == CloudType::Bridge)
                    .count()
            );
            println!(
                "Leaf clouds: {}",
                cloud_partition
                    .start
                    .iter_1()
                    .filter(|n| cloud_partition.cloud_type(*n) == CloudType::Leaf)
                    .count()
            );

            let mut f = None;
            let dot_string;

            if !cli.get_flag("partition") {
                let start = ProcessTime::now();
                f = Some(GraphCoarsening::new(&cloud_partition));
                let time_f = start.elapsed();

                println!();
                println!("Graph Coarsening finished, took {:?}", time_f);
                println!(
                    "Number of nodes in coarsened graph: {}",
                    f.clone().unwrap().f.nodes
                );
            }

            if let Some(output_file) = cli.get_one::<String>("output") {
                if cli.get_flag("partition") {
                    println!("Error: The -o flag cannot be used with the -p flag.");
                    return;
                }

                println!("Writing to file {}", output_file);
                f.clone()
                    .unwrap()
                    .f
                    .write_to_file(output_file)
                    .expect("could not write to output file");
            }

            if let Some(output_file) = cli.get_one::<String>("visualize") {
                if graph.nodes > 500 {
                    println!("Error: The graph is too large to be visualized. Please use a smaller graph or remove the -v flag.");

                    return;
                }

                println!();
                println!("Writing visualization to file {}", output_file);
                match f {
                    Some(f) => dot_string = dot_graph(&f.f, &[]),
                    None => {
                        dot_string = {
                            let subgraphs: Vec<Vec<usize>> = cloud_partition
                                .start
                                .iter_1()
                                .map(|n| cloud_partition.cloud(n))
                                .collect();
                            dot_graph(&graph, &subgraphs)
                        }
                    }
                }

                fs::write(output_file, dot_string)
                    .expect("Error: could not write to visualization file")
            };
        }
    }
}

fn load_program_data() -> Command {
    Command::new("StaR CLI")
        .version("0.1.0")
        .about("StaR is a library offering graph algorithms such as BFS and DFS and an algorithm for graph coarsening. This CLI computes a coarsened graph for a given input graph. For information on the input graph format and the output format, please refer to the README.")
        .args([arg!(file: <file> "Path to input graph"), 
               arg!(output: -o --output <output_file>"Path to output file, will not work with -p"), 
               arg!(partition: -p --partition "Only calculate the cloud partition of the graph, will not work with -o"),
               arg!(visualize: -v --visualize <output_file> "Visualize the graph in DOT format. Only recommended for small input graphs with up to 500 nodes.")
            ])
}

fn read_graph(file: &str) -> Result<Graph, Error> {
    let file = File::open(file)?;
    let buf_read = BufReader::new(file);

    Graph::try_from(buf_read)
}
