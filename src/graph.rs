use std::{collections::VecDeque, vec, cmp::Reverse};

pub struct AdjacencyList<E: Copy> {
    edges: Vec<Vec<(usize, E)>>,
    vertices: usize,
}

// pub struct KeyAndData<K: Copy + Eq + Ord, D> {
//     pub key: K,
//     pub data: D,
// }

// impl<K: Copy + Eq + Ord, D> PartialEq for KeyAndData<K, D> {
//     fn eq(&self, other: &Self) -> bool {
//         self.key.eq(&other.key)
//     }
// }

// impl<K: Copy + Eq + Ord, D> Eq for KeyAndData<K, D> {}

// impl<K: Copy + Ord, D> PartialOrd for KeyAndData<K, D> {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         self.key.partial_cmp(&other.key)
//     }
// }

// impl<K: Copy + Ord, D> std::cmp::Ord for KeyAndData<K, D> {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         self.key.cmp(&other.key)
//     }
// }

impl<E: Copy> AdjacencyList<E> {
    pub const fn new() -> Self {
        Self {
            edges: Vec::new(),
            vertices: 0,
        }
    }

    pub fn reserved(vertices: usize) -> Self {
        Self {
            edges: Vec::with_capacity(vertices),
            vertices: 0,
        }
    }

    pub fn add_edge(&mut self, from: usize, to: usize, weight: E) {
        self.vertices = self.vertices.max(from.max(to) + 1);
        self.edges.resize_with(self.vertices, Vec::new);
        self.edges[from].push((to, weight));
    }

    pub fn add_edge_undirected(&mut self, from: usize, to: usize, weight: E) {
        self.add_edge(from, to, weight);
        self.add_edge(to, from, weight);
    }

    fn dfs_print(&self, start: usize) {
        let mut visited = vec![false; self.vertices];
        let mut stack = vec![start];
        let mut loop_count = 0;
        visited[start] = true;
        while let Some(current) = stack.pop() {
            // if visited[current] {
            //     continue;
            // }
            // visited[current] = true;
            println!("Visiting vertex {}", current);
            stack.extend(self.edges[current].iter().filter_map(|(to, _)| {
                loop_count += 1;
                println!("count: {loop_count}");
                if visited[*to] {
                    None
                } else {
                    visited[*to] = true;
                    Some(*to)
                }
            }));
        }
    }
    pub fn dfs(&self, start: usize) -> Dfs {
        let mut visited = vec![false; self.vertices];
        let stack = vec![];
        let current = start;
        visited[current] = true;
        Dfs {
            visited,
            stack,
            current: Some(current),
        }
    }

    pub fn dfs_label<L: Default>(
        &self,
        start: usize,
        label: L,
        mut f: impl FnMut(&L, &L, &E) -> (L, bool),
    ) {
        let mut stack = vec![start];
        let mut labels: Vec<L> = (0..self.edges.len()).map(|_| Default::default()).collect();
        labels[start] = label;
        while let Some(current) = stack.pop() {
            println!("Visiting vertex {}", current);
            stack.extend(self.edges[current].iter().filter_map(|(to, edge)| {
                let (l, c) = f(&labels[current], &labels[*to], edge);
                labels[*to] = l;
                if c {
                    Some(*to)
                } else {
                    None
                }
            }))
        }
    }

    fn bfs_print(&self, start: usize) {
        let mut visited = vec![false; self.vertices];
        let mut queue = VecDeque::from([start]);
        let mut loop_count = 0;
        while let Some(current) = queue.pop_front() {
            if visited[current] {
                continue;
            }
            visited[current] = true;
            println!("Visiting vertex {}", current);
            queue.extend(self.edges[current].iter().filter_map(|(to, _)| {
                loop_count += 1;
                println!("count: {loop_count}");
                if visited[*to] {
                    None
                } else {
                    Some(*to)
                }
            }));
        }
    }

    pub fn bfs(&self, start: usize) -> Bfs {
        let mut visited = vec![false; self.vertices];
        let queue = VecDeque::new();
        let current = start;
        visited[current] = true;
        Bfs {
            visited,
            queue,
            current: Some(current),
        }
    }
}

impl AdjacencyList<u32> {
    fn dijkstra(&self, start: usize) {
        let mut distances = vec![std::u32::MAX; self.vertices];
        let mut confirmed = vec![false; self.vertices];
        let mut pqueue = std::collections::BinaryHeap::from([(Reverse(0u32), start)]);
        distances[start] = 0;
        confirmed[start] = true;
        while let Some((Reverse(distance), current)) = pqueue.pop() {
            confirmed[current] = true;
            println!("Visiting vertex {}", current);
            println!("distance: {distance}");
            pqueue.extend(self.edges[current].iter().filter_map(|(to, edge)| {
                if confirmed[*to] {
                    None
                } else {
                    distances[*to] = distances[*to].min(distance + *edge);
                    Some((Reverse(distances[*to]), *to))
                }
            }))
        }
    }
}
pub struct Dfs {
    visited: Vec<bool>,
    stack: Vec<usize>,
    current: Option<usize>,
}
pub struct Bfs {
    visited: Vec<bool>,
    queue: VecDeque<usize>,
    current: Option<usize>,
}

pub trait Container<T> {
    fn push(&mut self, values: impl IntoIterator<Item = T>);
    fn pop(&mut self) -> Option<T>;
}

pub struct Stack<T>(Vec<T>);
impl<T> Container<T> for Stack<T> {
    fn push(&mut self, values: impl IntoIterator<Item = T>) {
        self.0.extend(values);
    }
    fn pop(&mut self) -> Option<T> {
        self.0.pop()
    }
}

pub struct Queue<T>(VecDeque<T>);
impl<T> Container<T> for Queue<T> {
    fn push(&mut self, values: impl IntoIterator<Item = T>) {
        self.0.extend(values);
    }
    fn pop(&mut self) -> Option<T> {
        self.0.pop_front()
    }
}

pub trait LabelUpdate<L, WE> {
    fn adj_label(&mut self, label_current: &L, label_adj: &L, weight_edge: &WE) -> (L, bool);
}

pub struct VertexSearcher<L, C: Container<usize>, LU> {
    labels: Vec<L>,
    container: C,
    current: Option<usize>,
    label_updater: LU,
}

/// 隣接する頂点を検知済みとし、すでに検知済みの頂点はpushしない
pub struct MarkVertex;

impl<WE> LabelUpdate<bool, WE> for MarkVertex {
    fn adj_label(&mut self, _: &bool, label_adj: &bool, _: &WE) -> (bool, bool) {
        (true, !*label_adj)
    }
}

impl<L, C: Container<usize>, LU> VertexSearcher<L, C, LU> {
    pub fn next<WE: Copy>(&mut self, graph: &AdjacencyList<WE>) -> Option<usize>
    where
        LU: LabelUpdate<L, WE>,
    {
        self.current.map(|current| {
            self.container
                .push(graph.edges[current].iter().filter_map(|(to, we)| {
                    let (l, c) =
                        self.label_updater
                            .adj_label(&self.labels[current], &self.labels[*to], we);
                    self.labels[*to] = l;
                    if c {
                        Some(*to)
                    } else {
                        None
                    }
                }));
            self.current = self.container.pop();
            current
        })
    }
}

impl Dfs {
    pub fn next<E: Copy>(&mut self, graph: &AdjacencyList<E>) -> Option<usize> {
        self.current.map(|current| {
            self.stack
                .extend(graph.edges[current].iter().filter_map(|(to, _)| {
                    if self.visited[*to] {
                        None
                    } else {
                        self.visited[*to] = true;
                        Some(*to)
                    }
                }));
            self.current = self.stack.pop();
            current
        })
    }
}

impl Bfs {
    pub fn next<E: Copy>(&mut self, graph: &AdjacencyList<E>) -> Option<usize> {
        self.current.map(|current| {
            self.queue
                .extend(graph.edges[current].iter().filter_map(|(to, _)| {
                    if self.visited[*to] {
                        None
                    } else {
                        Some(*to)
                    }
                }));
            while let Some(next) = self.queue.pop_front() {
                if self.visited[next] {
                    continue;
                }
                self.visited[next] = true;
                self.current = Some(next);
                return current;
            }
            self.current = None;
            current
        })
    }
}

mod algo {
    use super::AdjacencyList;
}
#[cfg(test)]
mod test {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn test_dfs() {
        let mut graph: AdjacencyList<i32> = AdjacencyList::reserved(7);
        graph.add_edge_undirected(0, 1, 1);
        graph.add_edge_undirected(0, 2, 1);
        graph.add_edge_undirected(1, 3, 1);
        graph.add_edge_undirected(2, 3, 1);
        graph.add_edge_undirected(3, 4, 1);
        graph.add_edge_undirected(2, 6, 1);
        graph.add_edge_undirected(4, 5, 1);
        graph.add_edge_undirected(5, 6, 1);

        let start = 2;
        let mut dfs = graph.dfs(start);
        while let Some(current) = dfs.next(&graph) {
            println!("Visiting vertex {}", current);
        }

        println!();
        graph.dfs_print(start);

        graph.dfs_label(start, true, |_, l, _| (true, !*l));
    }

    #[test]
    fn test_bfs() {
        let mut graph: AdjacencyList<i32> = AdjacencyList::reserved(7);
        graph.add_edge_undirected(0, 1, 1);
        graph.add_edge_undirected(0, 2, 1);
        graph.add_edge_undirected(1, 3, 1);
        graph.add_edge_undirected(2, 3, 1);
        graph.add_edge_undirected(3, 4, 1);
        graph.add_edge_undirected(2, 6, 1);
        graph.add_edge_undirected(4, 5, 1);
        graph.add_edge_undirected(5, 6, 1);
        let mut bfs = graph.bfs(3);
        while let Some(current) = bfs.next(&graph) {
            println!("Visiting vertex {}", current);
        }
    }

    #[test]
    fn test_dijkstra() {
        let mut graph: AdjacencyList<u32> = AdjacencyList::reserved(7);
        graph.add_edge(0, 1, 2);
        graph.add_edge(0, 2, 1);
        graph.add_edge(1, 3, 3);
        graph.add_edge(2, 3, 4);
        graph.add_edge(3, 4, 1);
        graph.add_edge(2, 6, 1);
        graph.add_edge(4, 5, 3);
        graph.add_edge(5, 6, 6);
        graph.dijkstra(0);
    }
}
