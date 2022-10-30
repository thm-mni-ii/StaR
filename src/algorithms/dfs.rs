use crate::data_structures::graph::Graph;

pub fn depth_first_search(g: &Graph) {
    let mut colors = vec![0 as u8; g.nodes.len()]; // white
    for n in 0..(g.nodes.len()) {
        if colors[g.nodes[n] as usize] == 0 {
            process(g, n as u32, &mut colors);
        }
    }
}

fn process(g: &Graph, n: u32, colors: &mut Vec<u8>) {
    let mut stack: Vec<(u32, u32)> = Vec::with_capacity(g.nodes.len());
    let mut pos = 0;
    push_to_stack(&mut pos, &mut stack, (n, 1));

    while stack.len() != 0 {
        let temp = pop_from_stack(&mut stack, colors);
        colors[temp.0 as usize] = 1; // gray
        let neighbors = g.neighbors(temp.0);

        if temp.1 <= (neighbors.len() as u32) {
            push_to_stack(&mut pos, &mut stack, (temp.0, temp.1 + 1)); 

            if colors[neighbors[temp.1 as usize] as usize] == 0 {
                push_to_stack(&mut pos, &mut stack, (neighbors[temp.1 as usize], 1));
            }

        } else {
            colors[temp.0 as usize] = 2; // black
        }
        
    }

}

pub fn push_to_stack(pos: &mut usize, stack: &mut Vec<(u32, u32)>, to_push: (u32, u32)) {
    if *pos >= stack.len() {
        for i in 0..(stack.len() / 2) {
            stack[i] = (0, 0);
        }
        stack[0] = to_push;
        *pos = 1;
    }
    stack[*pos] = to_push;
    *pos += 1;
}

pub fn pop_from_stack(stack: &mut Vec<(u32, u32)>, colors: &mut Vec<u8>) -> (u32, u32) {
    if stack.len() == 0 {
        restore_segment(colors, stack);
    }
    stack.pop().unwrap()
}

fn restore_segment(colors: &mut Vec<u8>, stack: &mut Vec<(u32, u32)>) {
    for c in colors {
        if *c == (1 as u8) {
            *c = 0;
        }
    }

    //TODO: dfs neu starten bis S' und T gleich sind(wie komm ich auf t?)
}

#[cfg(test)]
mod tests {
    
}
