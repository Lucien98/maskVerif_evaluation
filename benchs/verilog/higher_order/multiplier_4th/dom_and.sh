read_verilog dom_and_4th_order.v;

hierarchy -check -top dom_and;
proc;
flatten;
opt;
memory;
opt;
techmap;
opt;

write_ilang dom_and.ilang
