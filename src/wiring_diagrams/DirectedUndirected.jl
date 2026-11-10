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

input_ports(d::HasDUWD) = subpart(d, :outer_in_port_type) |> collect
output_ports(d::HasDUWD) = subpart(d, :outer_out_port_type) |> collect

set_input_ports!(d::HasDUWD, input_ports::AbstractVector) =
  set_subpart!(d, :outer_in_port_type, input_ports)
set_output_ports!(d::HasDUWD, output_ports::AbstractVector) =
  set_subpart!(d, :outer_out_port_type, output_ports)
add_input_ports!(d::HasDUWD, input_ports::AbstractVector) =
  add_parts!(d, :OuterInPort, length(input_ports),
             outer_in_port_type = input_ports)
add_output_ports!(d::HasDUWD, output_ports::AbstractVector) =
  add_parts!(d, :OuterOutPort, length(output_ports),
             outer_out_port_type = output_ports)

function input_ports(d::HasDUWD, b::Int)
  if b == input_id(d)
    error("Input vertex does not have input ports within wiring diagram")
  elseif b == output_id(d)
    output_ports(d)
  else
    subpart(d, incident(d, b, :in_port_box), :in_port_type) |>
      collect # Copy for backwards compatibilty.
  end
end

function output_ports(d::HasDUWD, b::Int)
  if b == input_id(d)
    input_ports(d)
  elseif b == output_id(d)
    error("Output vertex does not have output ports within wiring diagram")
  else
    subpart(d, incident(d, b, :out_port_box), :out_port_type) |>
      collect # Copy for backwards compatibilty.
  end
end

function port_value(d::HasDUWD, port::Port)
  if port.box == input_id(d)
    subpart(d, port.port, :outer_in_port_type)
  elseif port.box == output_id(d)
    subpart(d, port.port, :outer_out_port_type)
  else
    port_id   = port.kind == InputPort ? in_port_id : out_port_id
    type_expr = port.kind == InputPort ? :in_port_type : :out_port_type
    subpart(d, port_id(d, port), type_expr)
  end
end

# Mutators
#---------
#TODO
add_box!(d::AbstractDUWD; data...) = add_part!(d, :Box; data...)

function add_box!(d::AbstractDUWD, undirected_port_types::AbstractVector{T},
  directed_in_types::AbstractVector{T},
  directed_out_types::AbstractVector{T}; data...)
  box = add_box!(d; data...)

  nUndirectedPorts = length(undirected_port_types)
  undirectedPorts = add_parts!(d, :Port, nUndirectedPorts, box=fill(box, nUndirectedPorts),
                     port_type=undirected_port_types)

  nDirectedInPorts = length(directed_in_types)
  directedInPorts = add_parts!(d, :InPort, nDirectedInPorts, in_port_box=fill(box, nDirectedInPorts),
                     in_port_type=directed_in_types)

  nDirectedOutPorts = length(directed_out_types)
  directedOutPorts = add_parts!(d, :OutPort, nDirectedOutPorts, out_port_box=fill(box, nDirectedOutPorts),
                     out_port_type=directed_out_types)

  box
end



#UWD mutators
add_junction!(d::AbstractDUWD; data...) = add_part!(d, :Junction; data...)
add_junction!(d::AbstractDUWD, type; data...) =
  add_part!(d, :Junction; junction_type=type, data...)

add_junctions!(d::AbstractDUWD, njunctions::Int; data...) =
  add_parts!(d, :Junction, njunctions; data...)
add_junctions!(d::AbstractDUWD, types::AbstractVector; data...) =
  add_parts!(d, :Junction, length(types); junction_type=types, data...)

function set_junction!(d::AbstractDUWD, port, junction; outer::Bool=false)
  if has_subpart(d, :junction_type)
    ptype = port_type(d, port, outer=outer)
    jtype = isempty(junction) ? nothing : junction_type(d, junction)
    all(ptype .== jtype) || error(
      "Domain error: port type $ptype and junction type $jtype do not match")
  end
  set_subpart!(d, port, outer ? :outer_junction : :junction, junction)
end
set_junction!(d::AbstractDUWD, junction; kw...) =
  set_junction!(d, :, junction; kw...)

function set_junction!(d::AbstractDUWD, port::Tuple{Int,Int}, junction)
  box, nport = port
  if box == outer_box(d)
    set_junction!(d, nport, junction, outer=true)
  else
    set_junction!(d, ports(d, box)[nport], junction)
  end
end

function add_wire!(d::AbstractDUWD, port1::Tuple{Int,Int}, port2::Tuple{Int,Int})
  j1, j2 = junction(d, port1), junction(d, port2)
  if j1 > 0
    set_junction!(d, port2, j1)
  elseif j2 > 0
    set_junction!(d, port1, j2)
  else
    j = has_subpart(d, :junction_type) ?
      add_junction!(d, port_type(d, port1)) : add_junction!(d)
    set_junction!(d, port1, j)
    set_junction!(d, port2, j)
  end
end
add_wire!(d, wire::Pair) = add_wire!(d, first(wire), last(wire))

function add_wires!(d::AbstractDUWD, wires)
  for wire in wires
    add_wire!(d, wire)
  end
end

#DWD mutators
# Graph mutation
function add_wire!(d::AbstractDUWDm, wire::DirectedWiringDiagrams.Wire)
  validate_ports(port_value(d, wire.source), port_value(d, wire.target))
  if wire.source.box == input_id(d) && wire.target.box == output_id(d)
    add_part!(d, :PassWire, pass_wire_value = wire.value,
              pass_src = wire.source.port,
              pass_tgt = wire.target.port)
  elseif wire.source.box == input_id(d)
    add_part!(d, :InWire, in_wire_value = wire.value,
              in_src = wire.source.port,
              in_tgt = in_port_id(d, wire.target))
  elseif wire.target.box == output_id(d)
    add_part!(d, :OutWire, out_wire_value=wire.value,
              out_src = out_port_id(d, wire.source),
              out_tgt = wire.target.port)
  else
    add_part!(d, :Wire, wire_value=wire.value,
              src = out_port_id(d, wire.source),
              tgt = in_port_id(d, wire.target))
  end
end
add_wire!(d::AbstractDUWD, pair::Pair) = add_wire!(d, DirectedWiringDiagrams.Wire(pair))

function add_wires!(d::AbstractDUWD, wires)
  for wire in wires
    add_wire!(d, wire)
  end
end

function rem_box!(d::AbstractDUWD, b::Int)
  rem_boxes!(d, b:b)
end

function rem_boxes!(d::AbstractDUWD, bs::AbstractVector{Int})
  #DWD components
  @assert all(1 <= b <= nboxes(d) for b in bs)

  # Remove associated directed wires.
  rem_parts!(d, :InWire, incident_reduce(d, bs, [:in_tgt, :in_port_box]))
  rem_parts!(d, :OutWire, incident_reduce(d, bs, [:out_src, :out_port_box]))
  rem_parts!(d, :Wire, incident_reduce(d, bs, [:tgt, :in_port_box]))
  rem_parts!(d, :Wire, incident_reduce(d, bs, [:src, :out_port_box]))

  # Remove associated directed ports.
  rem_parts!(d, :InPort, incident_reduce(d, bs, [:in_port_box]))
  rem_parts!(d, :OutPort, incident_reduce(d, bs, [:out_port_box]))

  #UWD components
  #TODO
  rem_parts!(d, :Port, incident_reduce(d, bs, [:box]))



  rem_parts!(d, :Box, bs)
end
rem_boxes!(d::AbstractDUWD, bs) = rem_boxes!(d, collect(Int, bs))

#TODO rem_wires
function rem_wire!(d::AbstractDUWD, wire::DirectedWiringDiagrams.Wire)
  if wire.source.box == input_id(d) && wire.target.box == output_id(d)
    for w in parts(d, :PassWire)
      subpart(d, w, :pass_wire_value) == wire.value &&
        subpart(d, w, :pass_src) == wire.source.port &&
        subpart(d, w, :pass_tgt) == wire.target.port &&
        return rem_part!(d, :PassWire, w)
    end
  elseif wire.source.box == input_id(d)
    for w in incident(d, in_port_id(d, wire.target), :in_tgt)
      subpart(d, w, :in_wire_value) == wire.value &&
        return rem_part!(d, :InWire, w)
    end
  elseif wire.target.box == output_id(d)
    for w in incident(d, out_port_id(d, wire.source), :out_src)
      subpart(d, w, :out_wire_value) == wire.value &&
        return rem_part!(d, :OutWire, w)
    end
  else
    for w in incident(d, out_port_id(d, wire.source), :src)
      subpart(d, w, :tgt) == in_port_id(d, wire.target) &&
        subpart(d, w, :wire_value) == wire.value &&
        return rem_part!(d, :Wire, w)
    end
  end
  error("Wire $wire does not exist, so cannot be removed")
end
rem_wire!(d::AbstractDUWD, pair::Pair) = rem_wire!(d, DirectedWiringDiagrams.Wire(pair))

function rem_wires!(d::AbstractDUWD, wires)
  for wire in wires
    rem_wire!(d, wire)
  end
end

function rem_wires!(d::AbstractDUWD, src::Int, tgt::Int)
  if src == input_id(d) && tgt == output_id(d)
    rem_parts!(d, :PassWire, parts(d, :PassWire))
  elseif src == input_id(d) 
    rem_parts!(d, :InWire, incident(d, tgt, [:in_tgt, :in_port_box]))
  elseif tgt == output_id(d)
    rem_parts!(d, :OutWire, incident(d, src, [:out_src, :out_port_box]))
  else
    wires = filter(w -> tgt_box(d,w) == tgt,
                   incident(d, src, [:src, :out_port_box]))
    rem_parts!(d, :Wire, wires)
  end
end
##

function add_outer_in_port!(d::AbstractDUWD, value)
  add_part!(d, :OuterInPort, outer_in_port_type=value)
end

function add_outer_out_port!(d::AbstractDUWD, value)
  add_part!(d, :OuterOutPort, outer_out_port_type=value)
end

#Graph properties: TODO


###################################################################
#UWD:
  #other constructors
  #operadic interface

#DWD
  #graph properties (?)
  #other constructors
  #operadic interface
  #substitution
  #Encapsulation

#graphviz



end