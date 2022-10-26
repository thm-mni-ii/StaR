pub struct Graph {
    pub nodes: Vec<u32>,
    pub edges: Vec<(u32, u32)>,
}

impl Graph {
    pub fn neighbors(&self, index: u32) -> Vec<u32> {
        let edges_containing_index: Vec<&(u32, u32)> = self.edges
            .iter()
            .filter(|e| e.0 == index || e.1 == index)
            .collect();
        let other_nodes: Vec<u32> = edges_containing_index
            .iter()
            .map(|e| if e.0 == index {e.1} else {e.0})
            .collect();

        other_nodes
    }

    pub fn add_node(&mut self, n: u32, edges: Vec<(u32, u32)>) {
        if !self.nodes.contains(&n) {
            self.nodes.push(n);
            edges.iter()
                .for_each(|e| self.edges.push(*e));
        } else {
            println!("Knoten {} existiert schon", n);
        }
    }

    pub fn remove_node(&mut self, node: u32) {
        if self.nodes.contains(&node) {
            self.nodes = self.nodes
                .iter()
                .filter(|n| **n != node)
                .map(|n| *n)
                .collect();
            self.edges = self.edges
                .iter()
                .filter(|n| n.0 != node && n.1 != node)
                .map(|n| *n)
                .collect();
        } else {
            print!("Knoten {} existiert nicht", node);
        }

    }

    pub fn add_edge(&mut self, e: (u32, u32)) {
        if !self.edges.contains(&e) {
            self.edges.push(e);
        } else {
            println!("Kante {:?} existiert schon", e);
        }
    }

    pub fn remove_edge(&mut self, edge: (u32, u32)) {
        if self.edges.contains(&edge) {
            self.edges = self.edges
                .iter()
                .filter(|e| edge.0 != e.0 || edge.1 != e.1)
                .map(|e| *e)
                .collect();
        } else {
            println!("Kante {:?} existiert nicht", edge);
        }
    }
}