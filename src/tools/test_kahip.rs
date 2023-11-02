use std::ptr;

use crate::data_structures::graph::Graph;

/* File: ./src/tools/kahip/kaHIP_interface.h */
extern "C" {
    fn kaffpa(
        n: &i32,
        vwgt: *mut i32,
        xadj: *mut Vec<usize>,
        adjcwgt: *mut i32,
        adjncy: *mut Vec<usize>,
        nparts: &i32,
        imbalance: &f64,
        suppress_output: bool,
        seed: i32,
        mode: i32,
        edgecut: *mut i32,
        part: *mut i32,
    );
}

pub unsafe fn kahip_test() {
    let mut graph = Graph::new_with_edges(
        18,
        vec![
            [1, 6].to_vec(),
            [0, 2, 7].to_vec(),
            [1, 3, 8].to_vec(),
            [2, 4, 9].to_vec(),
            [3, 5, 10].to_vec(),
            [4, 11].to_vec(),
            [0, 7, 12].to_vec(),
            [1, 6, 8, 13].to_vec(),
            [2, 7, 9, 14].to_vec(),
            [3, 8, 10, 15].to_vec(),
            [4, 9, 11, 16].to_vec(),
            [5, 10, 17].to_vec(),
            [6, 13].to_vec(),
            [7, 12, 14].to_vec(),
            [8, 13].to_vec(),
            [9].to_vec(),
            [10, 17].to_vec(),
            [11, 16].to_vec(),
        ],
    );
    let mut part = [0_i32; 18];
    kaffpa(
        &(graph.nodes as i32),
        ptr::null_mut(),
        graph.edges.as_mut_ptr(),
        ptr::null_mut(),
        graph.edges.as_mut_ptr(),
        &6,
        &0.5,
        false,
        1337,
        0,
        ptr::null_mut(),
        part.as_mut_ptr(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kahip() {
        unsafe { kahip_test() }
    }
}
