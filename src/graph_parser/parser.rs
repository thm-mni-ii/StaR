use crate::data_structures::graph::Graph;
use std::{
    fs::File,
    io::{BufRead, BufReader, ErrorKind},
};

//pub struct GraphReader<T: BufRead>(pub T);

impl TryFrom<BufReader<File>> for Graph {
    type Error = std::io::Error;

    fn try_from(reader: BufReader<File>) -> Result<Self, Self::Error> {
        //let reader = reader.0;
        let mut graph: Option<Graph> = None;
        let mut order: Option<usize> = None;
        for line in reader.lines() {
            let line = line?;
            let elements: Vec<_> = line.split(' ').collect();
            match elements[0] {
                "c" => {
                    // who cares about comments..
                }
                "p" => {
                    order = Some(parse_order(&elements)?);
                    graph = Some(Graph::new_with_nodes(order.unwrap()));
                }
                _ => match graph.as_mut() {
                    Some(graph) => {
                        let u = parse_vertex(elements[1], order.unwrap())?;
                        let v = parse_vertex(elements[2], order.unwrap())?;
                        graph.add_edge((u, v));
                    }
                    None => {
                        return Err(std::io::Error::new(
                            ErrorKind::Other,
                            "Edges encountered before graph creation",
                        ));
                    }
                },
            };
        }
        match graph {
            Some(graph) => Ok(graph),
            None => Err(std::io::Error::new(
                ErrorKind::Other,
                "No graph created during parsing",
            )),
        }
    }
}

fn parse_vertex(v: &str, order: usize) -> Result<usize, std::io::Error> {
    match v.parse::<usize>() {
        Ok(u) => {
            if u == 0 || u > order {
                Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "Invalid vertex label",
                ))
            } else {
                Ok(u - 1)
            }
        }
        Err(_) => Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid vertex label",
        )),
    }
}

fn parse_order(elements: &[&str]) -> Result<usize, std::io::Error> {
    if elements.len() < 3 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid line received starting with p",
        ));
    }
    match elements[2].parse::<usize>() {
        Ok(order) => Ok(order),
        Err(_) => Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid order of graph",
        )),
    }
}

#[cfg(test)]
mod tests {
    use crate::data_structures::graph::Graph;
    use std::{fs::File, io::BufReader};

    #[test]
    fn test_graph_reader() {
        let file = File::open("mygraph.txt").unwrap();
        let reader = BufReader::new(file);

        let graph = Graph::try_from(reader);

        print!("{:?}", graph);
    }
}

//Anmerkungen Graph Generator: es werden größere Knoten als oben angegeben generiert
//Knoten 0 erlaubt? Falls nein: es werden 0 generiert
