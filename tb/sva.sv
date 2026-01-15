module sva(
    input clk,
    logic MOSI, rst_n, SS_n, tx_valid,
    logic [7:0] tx_data,
    logic [9:0] rx_data,
    logic       rx_valid, MISO
);

// reset
miso_a    : assert property (miso_p);
miso_c    : cover  property (miso_p);
rx_valid_a: assert property(rx_valid_p);
rx_valid_c: cover  property(rx_valid_p);
rx_data_a : assert property(rx_data_p);
rx_data_c : cover  property(rx_data_p);

property miso_p;
    @(posedge clk) !rst_n |=> MISO == 0
endproperty
property rx_valid_p;
    @(posedge clk) !rst_n |=> rx_valid == 0
endproperty
property rx_data_p;
    @(posedge clk) !rst_n |=> rx_data == 0
endproperty

endmodule
