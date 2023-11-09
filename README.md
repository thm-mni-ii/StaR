# StaR

StaR is a library for space and time efficient graph algorithms. It contains a graph data structure and algorithms for BFS and DFS, as well as a graph coarsening algorithm.

## Features
- space efficient graph data structure
- BFS and DFS algorithms
- graph coarsening algorithm
- cloud partitioning algorithm

## CLI
The CLI can be used to test the graph coarsening algorithm, or only the cloud partitioning. It can be built using `cargo build --release --bin star-cli` and then used as follows:

```
Usage: star-cli [OPTIONS] <file>

Arguments:
  <file>  Path to input graph

Options:
  -o, --output <output_file>     Path to output file, will not work with -p
  -p, --partition                Only calculate the cloud partition of the graph, will not work with -o
  -v, --visualize <output_file>  Visualize the graph in DOT format. Only recommended for small input graphs with up to 500 nodes.
  -h, --help                     Print help
  -V, --version                  Print version
```

The output option will write the coarsened graph to the specified file in the format described below.The partition option will only calculate the cloud partition and print the number of clouds from all categories to stdout. The cloud partition can not be output, only visualized. The visualization option will write the graph to the specified file in DOT format and can visualize either the partitions of the graph or the coarsened graph. This option is only recommended for small input graphs with up to 500 nodes.
## Library Usage
To include this library in your Rust code you can add the following to your Cargo.toml:
```toml
[dependencies]
star = { git = "https://github.com/thm-mni-ii/StaR" }
```

## Input and Output Format
The CLI uses the format defined [here](http://www.inf.udec.cl/~jfuentess/datasets/graphs.php) for reading and writing graphs:
```
<Number of vertices>
<Number of edges>
<Source vertex> <Target vertex>
<Source vertex> <Target vertex>
...
```

## References
Graph coarsening / cloud partition algorithm:

[1] F. Kammer und J. Meintrup, „Space-Efficient Graph Coarsening with Applications to Succinct Planar Encodings“, 2022.

Space efficient DFS:

[2] A. Elmasry, T. Hagerup, und F. Kammer, „Space-efficient Basic Graph Algorithms“, S. 14 pages, 2015, doi: 10.4230/LIPICS.STACS.2015.288.

## License
This project is licensed under the MIT License, check [LICENSE](./LICENSE) file in this repository for more information.

