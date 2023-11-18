// #![feature(type_alias_impl_trait)]

pub trait Graph<IdxV> {
    fn adjacency(&self, v: IdxV) -> impl Iterator<Item = IdxV>;
}

pub trait MarkedGraph<IdxV, Marker>: Graph<IdxV> {
    fn marker_mut(&mut self, v: IdxV) -> &mut Marker;
    fn marker(&self, v: IdxV) -> &Marker;
}

pub trait WeightedGraph<IdxV, Weight> : Graph<IdxV> {
    fn adjacency_weight(&self, v: IdxV) -> impl Iterator<Item = (IdxV, Weight)>;
    fn adjacency(&self, v: IdxV) -> impl Iterator<Item = IdxV> {
        self.adjacency_weight(v).map(|(v, _)| v)
    }
}