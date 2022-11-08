use crate::data_structures::graph::Graph;

pub struct DFSPreprocess<'a> {
    pub graph: &'a Graph<'a>,
    pub stack: Vec<(usize, u32)>,
    pub t: Vec<(usize, u32)>,
    pub colors: Vec<u8>,
}

impl<'a> Iterator for DFSPreprocess<'a> {
    type Item = (&'a str, usize);

    fn next(&mut self) -> Option<Self::Item> {
        //println!("stack: {:?}, t: {:?}", self.stack, self.t);
        if self.stack.is_empty() {
            for i in 0..self.colors.len() {
                if self.colors[i] == 0 {
                    push_to_stack(&mut self.stack, &mut self.t, (i, 0));
                    return Some((self.graph.labels[i], i));
                    //break;
                }
            }
            if self.stack.is_empty() {
                return None;
            }
        }

        let temp = pop_from_stack(&mut self.stack, &mut self.t, &mut self.colors);
        self.colors[temp.0 as usize] = 1; // gray
        let neighbors = self.graph.neighbors(temp.0);

        if temp.1 < (neighbors.len() as u32) {
            push_to_stack(&mut self.stack, &mut self.t, (temp.0, temp.1 + 1));

            if self.colors[neighbors[temp.1 as usize] as usize] == 0 {
                push_to_stack(
                    &mut self.stack,
                    &mut self.t,
                    (neighbors[temp.1 as usize], 0),
                );
                return Some((self.graph.labels[neighbors[temp.1 as usize]], neighbors[temp.1 as usize]));
            }
        } else {
            self.colors[temp.0 as usize] = 2;
        }
        return self.next();
    }
}

pub fn push_to_stack(
    stack: &mut Vec<(usize, u32)>,
    t: &mut Vec<(usize, u32)>,
    to_push: (usize, u32),
) {
    if stack.len() >= stack.capacity() {
        println!("overflow");
        *stack = Vec::with_capacity(stack.capacity());
        *t = Vec::with_capacity(stack.capacity());
    }
    stack.push(to_push);

    if stack.len() == stack.capacity() || stack.len() == stack.capacity() / 2 {
        t.push(to_push);
    }
}

pub fn pop_from_stack(
    stack: &mut Vec<(usize, u32)>,
    t: &mut Vec<(usize, u32)>,
    colors: &mut Vec<u8>,
) -> (usize, u32) {
    if stack.len() == 0 && !t.is_empty() {
        restore_segment(colors);
    }
    if stack.len() == stack.capacity() || stack.len() == stack.capacity() / 2 {
        t.pop().unwrap();
    }
    stack.pop().unwrap()
}

fn restore_segment(colors: &mut Vec<u8>) {
    for c in colors {
        if *c == (1 as u8) {
            *c = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::data_structures::graph::Graph;

    #[test]
    fn test_dfs() {
        let graph = Graph {
            labels: vec!["1", "2", "3", "4", "5", "6"],
            nodes: vec![0, 0, 0, 0, 0, 0],
            edges: vec![(0, 3), (0, 2), (1, 4), (2, 1), (4, 1)],
        };

        //println!("{:?}", dfs.colors);
        graph.dfs_preprocess().for_each(|i| println!("{:?}", i))
    }
}
