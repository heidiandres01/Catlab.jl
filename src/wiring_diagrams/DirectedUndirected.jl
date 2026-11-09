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
#elements from DWD:
  #Port struct, Wire struct
import ..UndirectedWiringDiagrams
#elements from UWD:

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

#UWD accessors
outer_box(::HasDUWD) = 0
box(d::HasDUWD, args...) = subpart(d, args..., :box)
junction(d::HasDUWD, args...; outer::Bool=false) =
  subpart(d, args..., outer ? :outer_junction : :junction)

function junction(d::HasDUWD, port::Tuple{Int,Int})
  box, nport = port
  box == outer_box(d) ?
    junction(d, nport, outer=true) : junction(d, ports(d, box)[nport])
end

nboxes(d::HasDUWD) = nparts(d, :Box)
njunctions(d::HasDUWD) = nparts(d, :Junction)
boxes(d::HasDUWD) = parts(d, :Box)
junctions(d::HasDUWD) = parts(d, :Junction)

ports(d::HasDUWD; outer::Bool=false) = parts(d, outer ? :OuterPort : :Port)
ports(d::HasDUWD, box) =
  box == outer_box(d) ? parts(d, :OuterPort) : incident(d, box, :box)
ports_with_junction(d::HasDUWD, junction; outer::Bool=false) =
  incident(d, junction, outer ? :outer_junction : :junction)

junction_type(d::HasDUWD, args...) = subpart(d, args..., :junction_type)
port_type(d::HasDUWD, args...; outer::Bool=false) =
  subpart(d, args..., outer ? :outer_port_type : :port_type)

function port_type(d::HasDUWD, port::Tuple{Int,Int})
  box, nport = port
  box == outer_box(d) ?
    port_type(d, nport, outer=true) : port_type(d, ports(d, box)[nport])
end


#DWD accessors

#Basic accessors

#function box: see UWD accessors section
#boxes, nboxes: see UWD accessors section
box_ids(d::HasDUWD) = parts(d, :Box)

src_box(d::HasDUWD, w::Int) = subpart(d, w, [:src, :out_port_box])
tgt_box(d::HasDUWD, w::Int) = subpart(d, w, [:tgt, :in_port_box])
in_tgt_box(d::HasDUWD, w::Int) = subpart(d, w, [:in_tgt, :in_port_box])
out_src_box(d::HasDUWD, w::Int) = subpart(d, w, [:out_src, :out_port_box])

local_in_port_id(d::HasDUWD, b::Int, p::Int) =
  searchsortedfirst(incident(d, b, :in_port_box), p)
local_out_port_id(d::HasDUWD, b::Int, p::Int) =
  searchsortedfirst(incident(d, b, :out_port_box), p)

in_port_id(d::HasDUWD, b::Int, p::Int) = incident(d, b, :in_port_box)[p]
out_port_id(d::HasDUWD, b::Int, p::Int) = incident(d, b, :out_port_box)[p]

#p::Port refers to struct Port in Directed, not Port::Ob, the UWD component
in_port_id(d::HasDUWD, p::DirectedWiringDiagrams.Port) = in_port_id(d, p.box, p.port)
out_port_id(d::HasDUWD, p::DirectedWiringDiagrams.Port) = out_port_id(d, p.box, p.port)


# from Directed WiringDiagram struct section:
# input_id(::WiringDiagram) = -2
# output_id(::WiringDiagram) = -1
# outer_ids(::WiringDiagram) = (-2,-1)
input_id(::HasDUWD) = -2
output_id(::HasDUWD) = -1
outer_ids(::HasDUWD) = (-2,-1)
#

@inline DirectedWiringDiagrams.Wire(d::HasDUWD, type::Symbol, w::Int) = DirectedWiringDiagrams.Wire(d, Val{type}, w)

function DirectedWiringDiagrams.Wire(d::HasDUWD, ::Type{Val{:PassWire}}, w::Int)
  DirectedWiringDiagrams.Wire(subpart(d, w, :pass_wire_value),
       (input_id(d), subpart(d, w, :pass_src)) =>
       (output_id(d), subpart(d, w, :pass_tgt)))
end

function DirectedWiringDiagrams.Wire(d::HasDUWD, ::Type{Val{:InWire}}, w::Int)
  DirectedWiringDiagrams.Wire(subpart(d, w, :in_wire_value),
       (input_id(d),
        subpart(d, w, :in_src)) => 
       (in_tgt_box(d,w),
        local_in_port_id(d, in_tgt_box(d,w), subpart(d, w, :in_tgt))))
end

function DirectedWiringDiagrams.Wire(d::HasDUWD, ::Type{Val{:OutWire}}, w::Int)
  DirectedWiringDiagrams.Wire(subpart(d, w, :out_wire_value),
       (out_src_box(d,w),
        local_out_port_id(d, out_src_box(d,w), subpart(d, w, :out_src))) =>
       (output_id(d),
        subpart(d, w, :out_tgt)))
end

function DirectedWiringDiagrams.Wire(d::HasDUWD, ::Type{Val{:Wire}}, w::Int)
  DirectedWiringDiagrams.Wire(subpart(d, w, :wire_value),
       (src_box(d,w),
        local_out_port_id(d, src_box(d,w), subpart(d, w, :src))) =>
       (tgt_box(d,w),
        local_in_port_id(d, tgt_box(d,w), subpart(d, w, :tgt))))
end

function wires(d::HasDUWD, src::Int, tgt::Int)
  if src == input_id(d) && tgt == output_id(d)
    [DirectedWiringDiagrams.Wire(d, :PassWire, w) for w in parts(d, :PassWire)]
  elseif src == input_id(d)
    [DirectedWiringDiagrams.Wire(d, :InWire, w)
     for w in incident(d, tgt, [:in_tgt, :in_port_box])]
  elseif tgt == output_id(d)
    [DirectedWiringDiagrams.Wire(d, :OutWire, w)
     for w in incident(d, src, [:out_src, :out_port_box])]
  else
    [DirectedWiringDiagrams.Wire(d, :Wire, w) for w in incident(d, src, [:src, :out_port_box])
     if tgt_box(d,w) == tgt]
  end
end

wires(d::HasDUWD, type::Symbol) =
  [ DirectedWiringDiagrams.Wire(d, type, w) for w in parts(d, type) ]
wires(d::HasDUWD) = vcat(wires(d, :PassWire), wires(d, :InWire),
                               wires(d, :Wire), wires(d, :OutWire))


function nwires(d::HasDUWD, src::Int, tgt::Int)
  if src == input_id(d) && tgt == output_id(d)
    nparts(d, :PassWire)
  elseif src == input_id(d)
    length(incident(d, tgt, [:in_tgt, :in_port_box]))
  elseif tgt == output_id(d)
    length(incident(d, src, [:out_src, :out_port_box]))
  else
    count(w -> tgt_box(d,w) == tgt,
          incident(d, src, [:src, :out_port_box]))
  end
end

nwires(d::HasDUWD, type::Symbol) = nparts(d, type)
nwires(d::HasDUWD) = (nwires(d, :PassWire) + nwires(d, :InWire) +
                            nwires(d, :Wire) + nwires(d, :OutWire))

has_wire(d::HasDUWD, src::Int, tgt::Int) = nwires(d, src, tgt) > 0
has_wire(d::HasDUWD, wire::DirectedWiringDiagrams.Wire) =
  wire in wires(d, wire.source.box, wire.target.box)
has_wire(d::HasDUWD, pair::Pair) = has_wire(d, DirectedWiringDiagrams.Wire(pair))

##



###################################################################





end