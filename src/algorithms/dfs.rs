use crate::data_structures::graph::Graph;

pub fn depth_first_search_recursive(g: &Graph) {
    let mut colors = vec![0 as u8; g.nodes.len()];
    for n in 0..(g.nodes.len()) {
        if colors[g.nodes[n] as usize] == 0 {
            process_rec(g, n as u32, &mut colors);
        }
    }
}

fn process_rec(g: &Graph, n: u32, colors: &mut Vec<u8>) {
    colors[n as usize] = 1;

    let mut k = 0;
    let neighbors = g.neighbors(n);
    while k < neighbors.len() {
        let v = neighbors[k];
        if  colors[v as usize] == 0  {
            process_rec(g, v, colors);   
        }
        k = k + 1;
    }
    colors[n as usize]= 2;
}

pub fn depth_first_search_iter(g: &Graph) {
    let mut colors = vec![0 as u8; g.nodes.len()];
    for n in 0..(g.nodes.len()) {
        if colors[g.nodes[n] as usize] == 0 {
            process_iter(g, n as u32, &mut colors);
        }
    }
}

fn process_iter(g: &Graph, n: u32, colors: &mut Vec<u8>) {
    let mut stack = vec![(n, 1)];
    while stack.len() != 0 {
        let temp = stack.pop().unwrap();
        colors[temp.0 as usize] = 1;
        let neighbors = g.neighbors(temp.0);
        if temp.1 <= neighbors.len() {
            stack.push((temp.0, temp.1 + 1));
            if colors[neighbors[temp.1] as usize] == 0 {
                stack.push((neighbors[temp.1], 1));
            }
        } else {
            colors[temp.0 as usize] = 2;
        }
        
    }

}

#[cfg(test)]
mod tests {
    
}
