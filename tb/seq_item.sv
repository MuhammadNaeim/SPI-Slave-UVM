package seq_item_pkg;
import uvm_pkg::*;
import shared_pkg::*;
`include "uvm_macros.svh"
class slave_seq_item extends uvm_sequence_item;
`uvm_object_utils(slave_seq_item)
rand bit       rst_n, SS_n, MOSI, tx_valid;
rand bit [7:0] tx_data;
     bit [9:0] rx_data;
     bit       rx_valid, MISO;
// golden
     bit [9:0] rx_data_golden;
     bit       rx_valid_golden, MISO_golden;
// vars
rand   bit [10:0] mosi_arr; //   randomized array
static bit [10:0] mosi_bus; // unrandomized array
static bit [ 4:0] cycles;   // static counter
       bit [ 4:0] mosi_ptr;
// constructor
function new(string name = "slave_seq_item");
    super.new(name);
endfunction
// string
function string convert2string();
    return $sformatf("%s rst = 0b%0b, direction = 0b%0b", super.convert2string, rst_n, rx_data);
endfunction
function string convert2string_stimulus();
    return $sformatf("rst = 0b%0b, direction = 0b%0b", rst_n, rx_data);
endfunction

////////////////// constraints //////////////////
constraint reset_c {rst_n dist{0:=1, 1:=99};}
constraint mosi_bits_c {
    if (~SS_n) (mosi_arr[10:8] inside {3'b000, 3'b001, 3'b110, 3'b111});
}
constraint ss_n_c {
    if (cycles == 0)
        SS_n == 1;
    else
        SS_n == 0;
}
function void post_randomize();
    if (SS_n) mosi_bus = mosi_arr;
    MOSI = mosi_bus[mosi_ptr];
    if (cycles > 0)
        cycles--;
    else begin
        if (mosi_bus[10:8] == 3'b111) cycles = 23;
        else                          cycles = 13;
    end
    if (mosi_ptr > 0) begin
        mosi_ptr--;
    end
    else begin
        mosi_ptr = 5'd11;
    end
    // tx_valid constraint
    if (mosi_bus[10:8] == 3'b111)
        tx_valid = 1;
    else
        tx_valid = 0;
endfunction
endclass
endpackage
