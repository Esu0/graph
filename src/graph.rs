use std::{collections::VecDeque, vec};

pub struct AdjacencyList<V, E: Copy> {
    edges: Vec<Vec<(usize, E)>>,
    vertices: Vec<V>,
}

impl<V, E: Copy> AdjacencyList<V, E> {
    pub const fn new() -> Self {
        Self {
            edges: Vec::new(),
            vertices: Vec::new(),
        }
    }

    pub fn reserved(vertices: usize) -> Self {
        Self {
            edges: Vec::with_capacity(vertices),
            vertices: Vec::with_capacity(vertices),
        }
    }

    pub fn add_edge(&mut self, from: usize, to: usize, weight: E)
    where
        V: Default,
    {
        self.vertices
            .resize_with(from.max(to) + 1, Default::default);
        self.edges.resize_with(from.max(to) + 1, Vec::new);
        self.edges[from].push((to, weight));
    }

    pub fn add_edge_undirected(&mut self, from: usize, to: usize, weight: E)
    where
        V: Default,
    {
        self.add_edge(from, to, weight);
        self.add_edge(to, from, weight);
    }

    fn dfs_print(&self, start: usize) {
        let mut visited = vec![false; self.vertices.len()];
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
        let mut visited = vec![false; self.vertices.len()];
        let stack = vec![];
        let current = start;
        visited[current] = true;
        Dfs {
            visited,
            stack,
            current: Some(current),
        }
    }

    pub fn dfs_label<L>(&self, start: usize, label: L, mut f: impl FnMut(&L, &E) -> Option<L>) {
        let mut stack = vec![start];
        let mut labels: Vec<Option<L>> = (0..self.vertices.len()).map(|_| None).collect();
        labels[start] = Some(label);
        while let Some(current) = stack.pop() {
            if let Some(_) = &mut labels[current] {
                stack.extend(self.edges[current].iter().filter_map(|(to, edge)| {
                    if let Some(_) = &labels[*to] {
                        None
                    } else {
                        // safety: labels[i] can become None only if labels[i] is None.
                        // So, labels[current] is Some
                        labels[*to] =
                            f(unsafe { labels[current].as_ref().unwrap_unchecked() }, edge);
                        Some(*to)
                    }
                }))
            }
        }
    }
    fn bfs_print(&self, start: usize) {
        let mut visited = vec![false; self.vertices.len()];
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
        let mut visited = vec![false; self.vertices.len()];
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

trait Container<T> {
    fn push(&mut self, values: impl IntoIterator<Item = T>);
    fn pop(&mut self) -> Option<T>;
}

impl<T> Container<T> for Vec<T> {
    fn push(&mut self, values: impl IntoIterator<Item = T>) {
        self.extend(values);
    }
    fn pop(&mut self) -> Option<T> {
        self.pop()
    }
}

impl<T> Container<T> for VecDeque<T> {
    fn push(&mut self, values: impl IntoIterator<Item = T>) {
        self.extend(values);
    }
    fn pop(&mut self) -> Option<T> {
        self.pop_front()
    }
}

pub trait VertexSercher {}
impl Dfs {
    pub fn next<V, E: Copy>(&mut self, graph: &AdjacencyList<V, E>) -> Option<usize> {
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
    pub fn next<V, E: Copy>(&mut self, graph: &AdjacencyList<V, E>) -> Option<usize> {
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
impl<V, E: Copy> From<Vec<V>> for AdjacencyList<V, E> {
    fn from(vertices: Vec<V>) -> Self {
        Self {
            edges: vec![Vec::new(); vertices.len()],
            vertices,
        }
    }
}

impl<V, E: Copy, const N: usize> From<[V; N]> for AdjacencyList<V, E> {
    fn from(vertices: [V; N]) -> Self {
        Self {
            edges: vec![Vec::new(); N],
            vertices: vertices.into(),
        }
    }
}

mod algo {
    use super::AdjacencyList;

    pub fn dinic(mut graph: AdjacencyList<usize, u64>, s: usize, t: usize) {}
}
#[cfg(test)]
mod test {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn test_dfs() {
        let mut graph: AdjacencyList<(), i32> = AdjacencyList::reserved(7);
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
    }

    #[test]
    fn test_bfs() {
        let mut graph: AdjacencyList<(), i32> = AdjacencyList::reserved(7);
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
}
