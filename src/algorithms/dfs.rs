use crate::data_structures::graph::Graph;

pub fn depth_first_search(g: &Graph, preprocess: fn(stack: &mut Vec<(u32, u32)>, t: &mut Vec<(u32, u32)>) -> bool) {
    let mut colors = vec![0 as u8; g.nodes.len()]; // white
    for n in 0..(g.nodes.len() - 1) {
        if colors[g.nodes[n] as usize] == 0 {
            process(g, g.nodes[n as usize], &mut colors);
        }
    }
}

fn process(g: &Graph, n: u32, colors: &mut Vec<u8>) {
    let mut stack: Vec<(u32, u32)> = Vec::with_capacity(g.nodes.len());
    let mut t: Vec<(u32, u32)> = Vec::new();
    push_to_stack( &mut stack, &mut t, (n, 0));

    while stack.len() != 0 {
        println!("stack: {:?}, t: {:?}", stack, t);
        let temp = pop_from_stack(&mut stack, &mut t, colors, g);
        colors[temp.0 as usize] = 1; // gray
        let neighbors = g.neighbors(temp.0);

        if temp.1 < (neighbors.len() as u32) {
            push_to_stack( &mut stack, &mut t, (temp.0, temp.1 + 1)); 

            if colors[neighbors[temp.1 as usize] as usize] == 0 {
                push_to_stack(&mut stack, &mut t, (neighbors[temp.1 as usize], 0));
            }

        } else {
            colors[temp.0 as usize] = 2; // black
        }
        
    }

}

pub fn push_to_stack(stack: &mut Vec<(u32, u32)>, t: &mut Vec<(u32, u32)>, to_push: (u32, u32)) {
    if stack.len() >= stack.capacity() {
        println!("overflow");
        *stack= Vec::with_capacity(stack.capacity());
    }
    stack.push(to_push);

    if stack.len() == stack.capacity() || stack.len() == stack.capacity() / 2 {
        println!("stack länge: {}, kapazität: {}", stack.len(), stack.capacity());
        t.push(to_push);
    }
}

pub fn pop_from_stack(stack: &mut Vec<(u32, u32)>, t: &mut Vec<(u32, u32)>, colors: &mut Vec<u8>, g: &Graph) -> (u32, u32) {
    if stack.len() == 0 {
        //restore_segment(colors, t, stack, g);
    }
    if (stack.len() == stack.capacity() || stack.len() == stack.capacity() / 2) {
        t.pop().unwrap();
    }
    stack.pop().unwrap()
}

fn restore_segment(colors: &mut Vec<u8>,t: &mut Vec<(u32, u32)>, stack: &mut Vec<(u32, u32)>, g: &Graph) {
    for c in colors {
        if *c == (1 as u8) {
            *c = 0;
        }
    }

    depth_first_search(g, |stack: &mut Vec<(u32, u32)>, t: &mut Vec<(u32, u32)>| stack[stack.len() - 1] == t[t.len()-1])
}

#[cfg(test)]
mod tests {
    use crate::data_structures::graph::Graph;
    use super::depth_first_search;

    #[test]
    fn test_dfs() {
        let graph = Graph {
            nodes: vec![0, 1, 2, 3, 4, 5],
            edges: vec![(0, 2), (1, 2), (2, 1), (3, 4), (4, 0), (1, 1), (1, 2), (1, 3), (1, 4)],
        };
        depth_first_search(&graph, |_, _| true);
    }
}
