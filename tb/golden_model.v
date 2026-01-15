module golden_model (MOSI,MISO,SS_n,clk,rst_n,rx_data,rx_valid,tx_data,tx_valid);

localparam IDLE      = 3'b000;
localparam WRITE     = 3'b001;
localparam CHK_CMD   = 3'b010;
localparam READ_ADD  = 3'b011;
localparam READ_DATA = 3'b100;

input            MOSI, clk, rst_n, SS_n, tx_valid;
input      [7:0] tx_data;
output reg [9:0] rx_data;
output reg       rx_valid, MISO;


reg [2:0] cs , ns;
reg ADD_DATA_checker;
reg [3:0] counter1;
reg [3:0] counter2;

    //state memory
    always @(posedge clk)
    begin
        if(~rst_n)
            cs <= IDLE;
        else
            cs <= ns ;
    end

    //next state logic
    always @(*) begin
        case(cs)
            IDLE : begin
                if(SS_n)
                    ns = IDLE;
                else
                    ns = CHK_CMD;
            end
            CHK_CMD : begin
                if(SS_n)
                    ns = IDLE;
                else begin
                    if((MOSI == 0))
                        ns = WRITE;
                    else begin
                        if (ADD_DATA_checker)
                            ns = READ_ADD;
                        else
                            ns = READ_DATA;
                    end
                end
            end
            WRITE : begin
                if(SS_n)
                    ns = IDLE;
                else
                    ns = WRITE;
            end
            READ_ADD : begin
                if(SS_n)
                    ns = IDLE;
                else
                    ns = READ_ADD;
            end
            READ_DATA : begin
                if(SS_n)
                    ns = IDLE;
                else
                    ns = READ_DATA;
            end
        endcase
    end

    //output logic
    always @(posedge clk) begin
        if (~rst_n) begin
            counter1 <= 10;
            counter2 <= 8;
            ADD_DATA_checker <= 1;
            rx_data  <= 0;
            rx_valid <= 0;
            MISO     <= 0;
        end
        //IDLE state
        else begin
            if(cs == IDLE) begin
                rx_valid <= 0 ;
                counter1 <= 10;
                counter2 <= 8 ;
            end
            //WRITE state
            else if(cs == WRITE) begin
                if (counter1 > 0)begin
                    rx_data[counter1-1] <= MOSI;
                    counter1 <= counter1 - 1;
                end
                else begin
                    rx_valid <= 1;
                end
            end
            else if (cs == READ_ADD) begin
                if (counter1 > 0)begin
                    rx_data[counter1-1] <= MOSI;
                    counter1 <= counter1 - 1;
                end
                else begin
                    rx_valid <= 1;
                    ADD_DATA_checker <= 0;
                end
            end
        //READ_DATA state
            else if (cs == READ_DATA) begin
                if(tx_valid) begin
                    rx_valid <= 0;
                    if (counter2 > 0) begin
                        MISO <= tx_data[counter2-1];
                        counter2 <= counter2 - 1;
                    end
                    else
                        ADD_DATA_checker <= 1;
                end
                else begin
                    if (counter1 > 0)begin
                        rx_data[counter1-1] <= MOSI;
                        counter1 <= counter1 - 1;
                    end
                    else begin
                        rx_valid <= 1;
                        counter1 <= 10;
                    end
                end
            end
        end

    end
endmodule
