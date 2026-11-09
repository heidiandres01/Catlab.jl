"""
Data structure for undirected directed wiring diagrams.
"""
module DirectedUndirectedWiringDiagrams
#TODO add what to export
#export ...

#adding all using and import statements from Directed.jl and Undirected.jl
#Directed.jl
using StructEquality

using GATlab
using ...Graphs.BasicGraphs, ...CategoricalAlgebra.CSets
import ...CategoricalAlgebra: is_isomorphic
import ...Graphs: all_neighbors, neighbors, outneighbors, inneighbors

#Undirected.jl
# using GATlab
using ...BasicSets, ...CategoricalAlgebra
using ...Theories: dom, codom, compose, ⋅, id, oplus
import ..DirectedWiringDiagrams: box, boxes, nboxes, add_box!, add_wire!,
  add_wires!, singleton_diagram, ocompose, substitute


# import DWD, UWD.
import ..DirectedWiringDiagrams
import ..UndirectedWiringDiagrams

# Data types
############

@abstract_acset_type HasDUWD

@present SchDUWD(FreeSchema) begin
    #shared
    Box::Ob

    #UWD components
    Port::Ob
    OuterPort::Ob
    Junction::Ob

    box::Hom(Port, Box)
    junction::Hom(Port, Junction)
    outer_junction::Hom(OuterPort, Junction)
    
    #DWD components
    (InPort, OutPort, OuterInPort, OuterOutPort)::Ob
    (Wire, InWire, OutWire, PassWire)::Ob

    src::Hom(Wire, OutPort)
    tgt::Hom(Wire, InPort)
    in_src::Hom(InWire, OuterInPort)
    in_tgt::Hom(InWire, InPort)
    out_src::Hom(OutWire, OutPort)
    out_tgt::Hom(OutWire, OuterOutPort)
    pass_src::Hom(PassWire, OuterInPort)
    pass_tgt::Hom(PassWire, OuterOutPort)

    in_port_box::Hom(InPort, Box)
    out_port_box::Hom(OutPort, Box)
end

@abstract_acset_type AbstractDUWD <: HasDUWD
const DirectedUndirectedWiringDiagram = AbstractDUWD

# skipping untyped DUWD, since I couldn't find an untyped DWD

# typed DUWD
@present SchTypedDUWD <: SchDUWD begin
  Type::AttrType

  #UWD elements
  port_type::Attr(Port, Type)
  outer_port_type::Attr(OuterPort, Type)
  junction_type::Attr(Junction, Type)

  compose(junction, junction_type) == port_type
  compose(outer_junction, junction_type) == outer_port_type

  #DWD elements
  #removed 'PortValue::AttrType', changed 'PortValue' to 'Type'
  in_port_type::Attr(InPort, Type)
  out_port_type::Attr(OutPort, Type)
  outer_in_port_type::Attr(OuterInPort, Type)
  outer_out_port_type::Attr(OuterOutPort, Type)

  #note: DWD doesn't have :in_port_box or :out_port_box here. should I add them?
end

@acset_type TypedDUWD(SchTypedDUWD,
  index=[:box, :junction, :outer_junction,
  :src, :tgt, :in_src, :in_tgt, :out_src, :out_tgt, :pass_src, :pass_tgt])
  <: AbstractDUWD

#skipping AttributedWiringDiagram, since I can't find a comparison for UWD

function (::Type{DUWD})(undirected_port_types::AbstractVector{T},
  directed_in_types::AbstractVector{T},
  directed_out_types::AbstractVector{T}) where DUWD <: AbstractDUWD
  d = DUWD()
  nUndirectedPorts = length(undirected_port_types)
  nDirectedInPorts = length(directed_in_types)
  nDirectedOutPorts = length(directed_out_types)

  add_parts!(d, :OuterPort, nUndirectedPorts, outer_port_type=undirected_port_types)
  add_parts!(d, :OuterInPort, nDirectedInPorts, outer_in_port_type=directed_in_types)
  add_parts!(d, :OuterOutPort, nDirectedOutPorts, outer_out_port_type=directed_out_types)

  return d
end

DirectedUndirectedWiringDiagram(undirected_port_types::AbstractVector{T},
  directed_in_types::AbstractVector{T},
  directed_out_types::AbstractVector{T}) where T =
  TypedDUWD{T}(undirected_port_types, directed_in_types, directed_out_types)

# Imperative interface
######################

# Accessors
#----------

#STOPPED HERE###########################



###################################################################





end