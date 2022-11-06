use crate::data_structures::graph::Graph;

pub fn depth_first_search(g: &Graph, preprocess: fn(stack: &mut Vec<(u32, u32)>, t: &mut Vec<(u32, u32)>) -> bool) {
    let mut colors = vec![0 as u8; g.nodes.len()]; // white
    for n in 0..(g.nodes.len() - 1) {
        if colors[n] == 0 {
            process(g, n, &mut colors);
        }
    }
}

fn process(g: &Graph, node_index: usize, colors: &mut Vec<u8>) {
    let mut stack: Vec<(usize, u32)> = Vec::with_capacity(g.nodes.len());
    let mut t: Vec<(usize, u32)> = Vec::new();
    push_to_stack( &mut stack, &mut t, (node_index, 0));

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

pub fn push_to_stack(stack: &mut Vec<(usize, u32)>, t: &mut Vec<(usize, u32)>, to_push: (usize, u32)) {
    if stack.len() >= stack.capacity() {
        println!("overflow");
        *stack= Vec::with_capacity(stack.capacity());
    }
    stack.push(to_push);

    if stack.len() == stack.capacity() || stack.len() == stack.capacity() / 2 {
        t.push(to_push);
    }
}

pub fn pop_from_stack(stack: &mut Vec<(usize, u32)>, t: &mut Vec<(usize, u32)>, colors: &mut Vec<u8>, g: &Graph) -> (usize, u32) {
    if stack.len() == 0 {
        //restore_segment(colors, t, stack, g);
    }
    if stack.len() == stack.capacity() || stack.len() == stack.capacity() / 2 {
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
            labels: vec!["1".to_string(), "2".to_string(), "3".to_string(), "4".to_string(), "5".to_string(), "6".to_string()],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };
        depth_first_search(&graph, |_, _| true);
    }
}
