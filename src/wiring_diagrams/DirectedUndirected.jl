"""
Data structure for undirected directed wiring diagrams.
"""
module DirectedUndirectedWiringDiagrams
#export ...


# import ..DirectedWiringDiagrams: box, boxes, nboxes, add_box!, add_wire!,
    # add_wires!, singleton_diagram, ocompose, substitute

using ...CategoricalAlgebra

import ..DirectedWiringDiagrams
import ..UndirectedWiringDiagrams

@present SchDUWD(FreeSchema) begin
    #shared
    Box::ob

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



end