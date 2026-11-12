module TestDirectedUndirectedWiringDiagrams
using Test, Catlab
using Catlab.WiringDiagrams.DirectedUndirectedWiringDiagrams

const DUWD = DirectedUndirectedWiringDiagram
const DWD = DirectedWiringDiagrams

#UWD tests

# Imperative interface
######################

# skipping Untyped wiring diagrams.
#TODO add tests for basic accessors: nboxes, njunctions, box, ports,ports_with_junction,   

# Typed wiring diagrams.
d = DirectedUndirectedWiringDiagram([:X,:Y,:Z], Symbol[], Symbol[])
add_box!(d, [:X,:W], Symbol[], Symbol[]); add_box!(d, [:Y,:W], Symbol[], Symbol[]); add_box!(d, [:Z,:W], Symbol[], Symbol[])
add_junctions!(d, [:X,:Y,:Z,:W])
@test port_type(d, 1) == :X
@test port_type(d, [1,3,5]) == [:X,:Y,:Z]
@test port_type(d, 3, outer=true) == :Z
@test junction_type(d, 3) == :Z
set_junction!(d, [1,3,5], 1:3)
set_junction!(d, [2,4,6], 4)
set_junction!(d, 1:3, 1:3, outer=true)
@test junction(d, 1:6) == [1,4,2,4,3,4]
@test junction(d, 1:3, outer=true) == [1,2,3]
@test_throws ErrorException set_junction!(d, 1, 2)

# Interface for ports that is relative to their boxes.
d_previous = d
d = DirectedUndirectedWiringDiagram([:X,:Y,:Z], Symbol[], Symbol[])
add_box!(d, [:X,:W], Symbol[], Symbol[]); add_box!(d, [:Y,:W], Symbol[], Symbol[]); add_box!(d, [:Z,:W], Symbol[], Symbol[])
@test port_type(d, (1,1)) == :X
@test port_type(d, (2,1)) == :Y
add_wires!(d, (i,1) => (outer_box(d),i) for i in 1:3)
add_wire!(d, (1,2) => (2,2))
add_wire!(d, (2,2) => (3,2))
@test d == d_previous

# Other constructors
#-------------------
#TODO
# Singleton diagrams.
# d = DirectedUndirectedWiringDiagram([:X,:Y,:Z])
# add_box!(d, [:X,:Y,:Z])
# add_junctions!(d, [:X,:Y,:Z])
# set_junction!(d, 1:3); set_junction!(d, 1:3, outer=true)
# @test singleton_diagram(DUWD, [:X,:Y,:Z]) == d

# # Diagrams from cospans.
# @test cospan_diagram(DUWD, FinFunction(1:3), FinFunction(1:3), [:X,:Y,:Z]) ==
#   singleton_diagram(DUWD, [:X,:Y,:Z])
# @test cospan_diagram(DUWD, FinFunction(1:3), FinFunction(1:3)) ==
#   singleton_diagram(DUWD, 3)

# d = DirectedUndirectedWiringDiagram(1)
# add_box!(d, 2); add_junctions!(d, 1)
# set_junction!(d, [1,1]); set_junction!(d, 1, outer=true)
# @test cospan_diagram(DUWD, FinFunction([1,1]), FinFunction([1])) == d

# # Diagrams from functions: junctions only.
# d = DirectedUndirectedWiringDiagram(4)
# add_junctions!(d, 3)
# set_junction!(d, [1,2,2,3], outer=true)
# @test junction_diagram(DUWD, FinFunction([1,2,2,3])) == d

# # Operadic interface
# ####################

# f = DirectedUndirectedWiringDiagram(3)
# add_box!(f, 2); add_box!(f, 2); add_box!(f, 2)
# add_junctions!(f, 4)
# set_junction!(f, [1,4,2,4,3,4])
# set_junction!(f, 1:3, outer=true)

# g1 = DirectedUndirectedWiringDiagram(2)
# add_box!(g1, 1); add_box!(g1, 1)
# add_junctions!(g1, 2)
# set_junction!(g1, 1:2)
# set_junction!(g1, 1:2, outer=true)
# g2 = copy(g1)
# set_junction!(g2, 2:-1:1)

# h = DirectedUndirectedWiringDiagram(3)
# add_box!(h, 2); add_box!(h, 1); add_box!(h, 1); add_box!(h, 2)
# add_junctions!(h, 4)
# set_junction!(h, [1,4,4,2,3,4])
# set_junction!(h, 1:3, outer=true)
# @test ocompose(f,2,g2) == h
# @test ocompose(ocompose(f,1,g1),3,g2) == ocompose(ocompose(f,2,g2),1,g1)

# h = DirectedUndirectedWiringDiagram(3)
# for i in 1:6; add_box!(h, 1) end
# add_junctions!(h, 4)
# set_junction!(h, [1,4,4,2,3,4])
# set_junction!(h, 1:3, outer=true)
# @test ocompose(f, [g1,g2,g1]) == h




#DWD tests

A, B, C, D = [:A], [:B], [:C], [:D]
# f = Box(:f, A, B) -> Symbol[], A, B
# g = Box(:g, B, C) -> Symbol[], B, C
# h = Box(:h, C, D) -> Symbol[], C, D
const DirWire = DirectedWiringDiagrams.Wire
const DirPort = DirectedWiringDiagrams.Port
const DirInputPort = DirectedWiringDiagrams.InputPort
const DirOutputPort = DirectedWiringDiagrams.OutputPort

# Imperative interface
######################

# Operations on boxes
d = DUWD(Symbol[], A, C)
@test nboxes(d) == 0
# @test box(d, input_id(d)) == nothing
# @test box(d, output_id(d)) == nothing

fv = add_box!(d, Symbol[], A, B)
@test nboxes(d) == 1
@test input_ports(d, fv) == A
@test output_ports(d, fv) == B
rem_box!(d, fv)
@test nboxes(d) == 0

fv = add_box!(d, Symbol[], A, B)
gv = add_box!(d, Symbol[], B, C)
hv = add_box!(d, Symbol[], C, D)
@test nboxes(d) == 3
rem_boxes!(d, [fv,hv])
@test nboxes(d) == 1
@test input_ports(d, 1) == B
@test output_ports(d, 1) == C


# Operations on ports
d = DUWD(Symbol[], A, C)
fv = add_box!(d, Symbol[], A, B)
gv = add_box!(d, Symbol[], B, C)

@test input_ports(d, fv) == A
@test output_ports(d, fv) == B
@test input_ports(d, output_id(d)) == C
@test output_ports(d, input_id(d)) == A
@test_throws ErrorException input_ports(d, input_id(d))
@test_throws ErrorException output_ports(d, output_id(d))

@test port_value(d, DirPort(input_id(d),DirOutputPort,1)) == :A
@test port_value(d, DirPort(output_id(d),DirInputPort,1)) == :C
@test port_value(d, DirPort(fv,DirInputPort,1)) == :A
@test port_value(d, DirPort(fv,DirOutputPort,1)) == :B

# Operations on wires
@test nwires(d) == 0
@test !has_wire(d, fv, gv)
@test !has_wire(d, (fv,1) => (gv,1))

add_wire!(d, DirWire((input_id(d),1) => (fv,1)))
add_wire!(d, DirWire((fv,1) => (gv,1)))
add_wire!(d, DirWire((gv,1) => (output_id(d),1)))

@test nwires(d) == 3

@test has_wire(d, fv, gv)
@test has_wire(d, (fv,1) => (gv,1))
@test has_wire(d, input_id(d), fv) && !has_wire(d, input_id(d), gv)
@test has_wire(d, gv, output_id(d)) && !has_wire(d, fv, output_id(d))
@test !has_wire(d, input_id(d), output_id(d))

@test_throws ErrorException add_wire!(d, DirWire((gv,1) => (fv,1)))
@test wires(d) == map(DirWire, [
  (input_id(d),1) => (fv,1),
  (fv,1) => (gv,1),
  (gv,1) => (output_id(d),1),
])

d_orig = copy(d)
add_wires!(d, [fill(DirWire((input_id(d),1) => (fv,1)), 2);
               fill(DirWire((fv,1) => (gv,1)), 2);
               fill(DirWire((gv,1) => (output_id(d),1)), 2)])
rem_wire!(d, (fv,1) => (gv,1))
@test nwires(d, fv, gv) == 2
rem_wires!(d, fv, gv)
@test nwires(d, fv, gv) == 0
rem_wire!(d, (input_id(d),1) => (fv,1))
@test nwires(d, input_id(d), fv) == 2
rem_wires!(d, input_id(d), fv)
@test nwires(d, input_id(d), fv) == 0
rem_wire!(d, (gv,1) => (output_id(d),1))
@test nwires(d, gv, output_id(d)) == 2
rem_wires!(d, gv, output_id(d))
@test nwires(d, gv, output_id(d)) == 0
d = DUWD(Symbol[], A, A)
add_wires!(d, fill(DirWire((input_id(d),1) => (output_id(d),1)), 3))
rem_wire!(d, (input_id(d),1) => (output_id(d),1))
@test nwires(d, input_id(d), output_id(d)) == 2
rem_wires!(d, input_id(d), output_id(d))
@test nwires(d, input_id(d), output_id(d)) == 0
d = d_orig

# Shallow copies.
d_copy = copy(d)
rem_boxes!(d_copy, [fv,gv])
@test nboxes(d) == 2
@test nwires(d) == 3

# Graph properties.
d_graph = graph(d)
@test length(vertices(d_graph)) == nboxes(d) + 2
@test length(edges(d_graph)) == nwires(d)
@test subpart(d_graph, :box) == box_ids(d) ∪ outer_ids(d)

@test Set(all_neighbors(d, fv)) == Set([input_id(d), gv])
@test Set(all_neighbors(d, gv)) == Set([fv, output_id(d)])
@test neighbors(d, fv) == [gv]
@test outneighbors(d, fv) == [gv]
@test outneighbors(d, input_id(d)) == [fv]
@test isempty(outneighbors(d, output_id(d)))
@test inneighbors(d, gv) == [fv]
@test inneighbors(d, output_id(d)) == [gv]
@test isempty(inneighbors(d, input_id(d)))
@test wires(d, input_id(d)) == [ DWD.Wire((input_id(d),1) => (fv,1)) ]
@test wires(d, fv) == map(DWD.Wire, [
  ((input_id(d),1) => (fv,1)),
  ((fv,1) => (gv,1))
])
@test out_wires(d, fv) == [ DWD.Wire((fv,1) => (gv,1)) ]
@test out_wires(d, DWD.Port(fv,DWD.OutputPort,1)) == [ DWD.Wire((fv,1) => (gv,1)) ]
@test in_wires(d, gv) == [ DWD.Wire((fv,1) => (gv,1)) ]
@test in_wires(d, DWD.Port(gv,DWD.InputPort,1)) == [ DWD.Wire((fv,1) => (gv,1)) ]

# # Induced subgraph.
# d = WiringDiagram(A,D)
# fv, gv, hv = add_box!(d, f), add_box!(d, g), add_box!(d, h)
# add_wires!(d, Pair[
#   (input_id(d),1) => (fv,1),
#   (fv,1) => (gv,1),
#   (gv,1) => (hv,1),
#   (hv,1) => (output_id(d),1),
# ])
# sub = WiringDiagram(A, D)
# fv, gv = add_box!(sub, f), add_box!(sub, g)
# add_wires!(sub, Pair[
#   (input_id(sub),1) => (fv,1),
#   (fv,1) => (gv,1),
# ])
# @test induced_subdiagram(d, [fv, gv]) == sub

# # Substitution
# ##############

# sub = WiringDiagram(B,D)
# gv = add_box!(sub, g)
# hv = add_box!(sub, h)
# add_wires!(sub, Pair[
#   (input_id(sub),1) => (gv,1),
#   (gv,1) => (hv,1),
#   (hv,1) => (output_id(sub),1),
# ])
# d0 = WiringDiagram(A,D)
# fv = add_box!(d0, f)
# subv = add_box!(d0, sub)
# add_wires!(d0, Pair[
#   (input_id(d0),1) => (fv,1),
#   (fv,1) => (subv,1),
#   (subv,1) => (output_id(d0),1),
# ])
# @test boxes(d0) == [ f, sub ]
# @test boxes(sub) == [ g, h ]
# d = substitute(d0, subv)
# @test nboxes(d) == 3
# @test boxes(d) == [f, g, h]
# box_map = Dict(box(d,v).value => v for v in box_ids(d))
# @test nwires(d) == 4
# @test Set(wires(d)) == Set(map(Wire, [
#   (input_id(d),1) => (box_map[:f],1),
#   (box_map[:f],1) => (box_map[:g],1),
#   (box_map[:g],1) => (box_map[:h],1),
#   (box_map[:h],1) => (output_id(d),1),
# ]))

# # Encapsulation
# ###############

# d0 = WiringDiagram(A,D)
# fv = add_box!(d0, f)
# gv = add_box!(d0, g)
# hv = add_box!(d0, h)
# add_wires!(d0, Pair[
#   (input_id(d),1) => (fv,1),
#   (fv,1) => (gv,1),
#   (gv,1) => (hv,1),
#   (hv,1) => (output_id(d),1)
# ])

# d = encapsulate(d0, [fv,gv])
# @test nboxes(d) == 2
# @test sum(isa(b, WiringDiagram) for b in boxes(d)) == 1
# @test nwires(d) == 3
# sub = first(b for b in boxes(d) if isa(b, WiringDiagram))
# @test nboxes(sub) == 2
# @test boxes(sub) == [f, g]
# box_map = Dict(box(sub,v).value => v for v in box_ids(sub))
# @test Set(wires(sub)) == Set(map(Wire, [
#   (input_id(sub),1) => (box_map[:f],1),
#   (box_map[:f],1) => (box_map[:g],1),
#   (box_map[:g],1) => (output_id(sub),1),
# ]))

# d = encapsulate(d0, [fv,gv], discard_boxes=true, value=:e)
# @test boxes(d) == [ Box(:e, A, C), h ]
# box_map = Dict(box(d,v).value => v for v in box_ids(d))
# @test Set(wires(d)) == Set(map(Wire, [
#   (input_id(d),1) => (box_map[:e],1),
#   (box_map[:e],1) => (box_map[:h],1),
#   (box_map[:h],1) => (output_id(d),1),
# ]))

# d0 = WiringDiagram(A,B)
# v1 = add_box!(d0, f)
# v2 = add_box!(d0, f)
# add_wires!(d0, Pair[
#   (input_id(d),1) => (v1,1),
#   (input_id(d),1) => (v2,1),
#   (v1,1) => (output_id(d),1),
#   (v2,1) => (output_id(d),1),
# ])
# d = encapsulate(d0, [v1,v2])
# @test nboxes(d) == 1
# @test nwires(d) == 2
# sub = first(boxes(d))
# @test sub == d0

# # Operadic interface
# ####################

# f, g, h = map([:f, :g, :h]) do sym
#   (i::Int) -> singleton_diagram(Box(Symbol("$sym$i"), [:A], [:A]))
# end

# # Identity
# d = compose(f(1),f(2))
# @test ocompose(g(1), 1, d) == d
# @test ocompose(g(1), [d]) == d
# @test ocompose(d, [f(1),f(2)]) == d
# @test ocompose(d, 1, f(1)) == d
# @test ocompose(d, 2, f(2)) == d

# # Associativity
# @test ocompose(compose(f(1),f(2)), [
#   ocompose(compose(g(1),g(2)), [compose(h(1),h(2)), compose(h(3),h(4))]),
#   ocompose(compose(g(3),g(4)), [compose(h(5),h(6)), compose(h(7),h(8))])
# ]) == ocompose(
#   ocompose(compose(f(1),f(2)), [compose(g(1),g(2)), compose(g(3),g(4))]),
#   [compose(h(1),h(2)), compose(h(3),h(4)), compose(h(5),h(6)), compose(h(7),h(8))]
# )
# @test ocompose(
#   ocompose(compose(f(1),f(2)), 1, compose(g(1),g(2))),
#   3, compose(g(3),g(4))
# ) == ocompose(
#   ocompose(compose(f(1),f(2)), 2, compose(g(3),g(4))),
#   1, compose(g(1),g(2))
# )





end # module
