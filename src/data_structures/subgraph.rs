use super::graph::Graph;

pub struct Subgraph<'a> {
    pub graph: &'a Graph,
    pub subset: Vec<bool>,
}

impl<'a> Subgraph<'a> {
    pub fn new(graph: &'a Graph, subset: Vec<bool>) -> Self {
        Subgraph { graph, subset }
    }

    pub fn add_to_subgraph(&mut self, node: usize) {
        if node >= self.graph.nodes.len() {
            panic!("node {} does not exist", node)
        }
        if self.graph.nodes[node] == 1 {
            panic!("node {} is invalid", node)
        }

        self.subset[node] = true;
    }

    pub fn remove_from_subgraph(&mut self, node: usize) {
        if node >= self.graph.nodes.len() {
            panic!("node {} does not exist", node)
        }

        self.subset[node] = false;
    }

    pub fn neighbors(&self, node: usize) -> Vec<usize> {
        if !self.subset[node] {
            panic!("node {} is not part of the subgraph", node);
        }

        self.graph
            .neighbors(node)
            .iter()
            .filter(|n| self.subset[**n])
            .copied()
            .collect()
    }
}

#[cfg(test)]
mod tests {}
