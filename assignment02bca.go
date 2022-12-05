package assignment02bca

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/gob"
	"fmt"
	"hash/fnv"
	"log"
	"math"
	"math/big"
	"net"
	"strconv"
	"strings"
	"sync"
)
const rnd = 5 //static, irl an aglo that increments this target over the period of time for incrs miners. want time and block rate to remain the same


type Block struct{
    Hash [] uint8 //an alias for the unsigned integer 8 type ( uint8 )
    Transactions [][] string
    PrevHash [] uint8
    Nonce int
    MerkleTreeRoot *MerkleTree
}

type BlockChain struct{ // type to represent the BC
    Blocks []*Block //array of pointer to blocks
    
}

type ProofOfWork struct{
    Block *Block
    Target *big.Int //target is the req described derived from rnd, big int for number larger than 64 bits
}

type MerkleTree struct {
	RootNode *MerkleNode
}

type MerkleNode struct {
	Left  *MerkleNode
	Right *MerkleNode
	Data  []byte
}



func NewMerkleNode(left, right *MerkleNode, data []byte) *MerkleNode {
	node := MerkleNode{}

	if left == nil && right == nil {
		hash := sha256.Sum256(data)
		node.Data = hash[:]
	} else {
		prevHashes := append(left.Data, right.Data...)
		hash := sha256.Sum256(prevHashes)
		node.Data = hash[:]
	}

	node.Left = left
	node.Right = right

	return &node
}

func NewMerkleTree(data [][]byte) *MerkleTree {
	var nodes []MerkleNode

	if len(data)%2 != 0 {
		data = append(data, data[len(data)-1])
	}

	for _, dat := range data {
		node := NewMerkleNode(nil, nil, dat)
		nodes = append(nodes, *node)
	}

	for i := 0; i < len(data)/2; i++ {
		var level []MerkleNode

		for j := 0; j < len(nodes); j += 2 {
			node := NewMerkleNode(&nodes[j], &nodes[j+1], nil)
			level = append(level, *node)
		}

		nodes = level
	}

	tree := MerkleTree{&nodes[0]}

	return &tree
}



func NewProof(b *Block) *ProofOfWork{ //outputs a pointer to POW and takes ptr to a block
    target := big.NewInt(1) //casting 1 as new BigInt converting any int to bigInt
    target.Lsh(target, uint(256-rnd)) //256 no. of uint8s in our hashes, use target to shift the number of uint8s over by this number, LSH (left shift func)
    
    pow := &ProofOfWork{b, target} //put the target into an instance of POW
    
    return pow //calculating the target for a block 
    
}

//utility function
func ToHex (num int64) [] byte{  //to add nonce to the collective hash for POW
    buff := new(bytes.Buffer) ////creates new bytes buffer. new used to get the Value representing a pointer to a new zero value for the specified type
    err := binary.Write(buff, binary.BigEndian, num) //encodes the num into bytes. Bytes to be organised in BigEndian
    if err != nil {
        log.Panic(err)
    }
    
    return buff.Bytes() //returning bytes portion of buffer
}

//creating hash of the target+block 

//hashcash - preceding 20 bits to be 0 in the hash
func (pow *ProofOfWork) InitData(nonce int) [] uint8{
    data := bytes.Join( //using Join to create a cohesive set of uint8s
        [][]uint8{
            pow.Block.PrevHash,
            pow.Block.HashTransactions(),
            ToHex(int64(nonce)),
            ToHex(int64(rnd)),
        },
        []uint8{}, //combined w uint8 to get  cohesive set of uint8s after combining everything to be returned
        )
    return data
}

//computational function 1-prepare data 2-convert to hash sha256 format 3-convert the hash into bigInt 4-compare the hash with our target bigInt inside of our POW struct
func (pow *ProofOfWork) MineBlock ()(int, []uint8){
    var intHash big.Int //to store hash in BigInt
    var hash [32]uint8
    
    nonce := 0
    
    for nonce < math.MaxInt64{ //virtually infinite loop
        data := pow.InitData(nonce) //1-preping the data
        hash = sha256.Sum256(data) //2- converting to hash
        
        intHash.SetBytes(hash[:])
        
        //4- compare to target
        if intHash.Cmp(pow.Target) == -1{   //hash>target, block mined
            break 
        } else {
            nonce++ 
        }
    }

    return nonce, hash[:]
    
}

//validate the block easier, than work portion being computationally expensive

func (pow *ProofOfWork) VerifyChain () bool{ //after the MineBlock func, we'll have the nonce that would allow us to calculate the hash that met the target that we wanted, 
    var intHash big.Int                                 //running that cycle one more time to show the hash is valid
    data := pow.InitData(pow.Block.Nonce)   //wrapping the data with the nonce calucltaed with pow
    
    hash := sha256.Sum256(data)
    intHash.SetBytes(hash[:])
    
    return intHash.Cmp(pow.Target) == -1 //<target
}

func hashString(s string) uint32 {
	h := fnv.New32a()
	h.Write([]byte(s))
	return h.Sum32()
}


func (b *Block) HashTransactions() []byte {
	var txHashes [][]byte

	for _, tx := range b.Transactions {

        tmpHash := hashString(strings.Join(tx, " "))
		a := make([]byte, 4)
		binary.LittleEndian.PutUint32(a, tmpHash)

		txHashes = append(txHashes, a)
	}

	tree := NewMerkleTree(txHashes)    
    
    b.MerkleTreeRoot = tree

	return tree.RootNode.Data
}


func NewBlock (data [][]string, prevHash [] uint8) *Block{  //takes data + prevHash of a block and outputs pointer to the next new block
    

	block := &Block{[]uint8{}, [][]string(data),prevHash, 0, &MerkleTree{}}  //using block constructor, for hash taking empty slice of uint8s, uint8(data) -> takes data string and converts it into uint8s, prevHash already passed as a uint8
    
    //performing pow for every block being created
    pow := NewProof (block)
    nonce, hash := pow.MineBlock()
    
    block.Hash = hash[:]
    block.Nonce = nonce
    return block
    
}


func Genesis() *Block{
    return NewBlock([][]string{{"Genesis"}}, []uint8{}) //empty slice of uint8s
}


//function to add the block to the chain
func(chain *BlockChain) AddBlock(transactions [][] string){ //method to add a block to the chain, hence it gets the pointer to the chain
    prevBlock := chain.Blocks[len(chain.Blocks)-1] //knowing the prev block
    newBlock := NewBlock(transactions, prevBlock.Hash) //calling NewBlock method to create the block
    chain.Blocks = append(chain.Blocks, newBlock) //appending newBlock and then assigning new blocks to blockchain.blocks
}

//creating a Blockchain from Genesis
func InitBlockChain() *BlockChain{
    return &BlockChain{[]*Block{Genesis()}} //reference to a BC, with an array of Block with a call to Genesis func
}



func DisplayBlocks(chain *BlockChain){
    //chain := blockchain.InitBlockChain()
    for _, block := range chain.Blocks{
        fmt. Printf("\n---------------------------------------\n")
        fmt. Printf("Previous Hash: %x\n", block.PrevHash)
        fmt. Printf("Transactions in Block:\n")
        for _, tx := range block.Transactions {
            fmt.Println(tx)
        }
        fmt.Println("Merkle Root Hash Pointer = ", block.MerkleTreeRoot)
        fmt. Printf("Hash: %x\n", block.Hash)
        //adding pow algo (consensus algo) to blocks
        pow := NewProof(block)
        fmt. Printf("Pow: %s\n", strconv.FormatBool(pow.VerifyChain())) //conv validation boolean output into string format
        fmt. Println()
        fmt. Printf("\n---------------------------------------\n")
       
    }
}


func changeBlock(chain *BlockChain, tx string, blockNo int){
   
    var newTransactions = chain.Blocks[blockNo].Transactions
    newTransactions = append(newTransactions, []string{tx})
    chain.Blocks[blockNo].Transactions = newTransactions


    // Re calculating the hash
    pow := NewProof (chain.Blocks[blockNo])
    nonce, hash := pow.MineBlock()
    
    chain.Blocks[blockNo].Hash = hash[:]
    chain.Blocks[blockNo].Nonce = nonce

    currentHash := hash[:]


    // Updating the next block's hash
    for key, _ := range chain.Blocks{
        if (key > blockNo){
            chain.Blocks[key].PrevHash = currentHash
            pow := NewProof (chain.Blocks[blockNo])
            nonce, hash := pow.MineBlock()
            chain.Blocks[key].Hash = hash[:]
            chain.Blocks[key].Nonce = nonce
            currentHash = hash[:]

        }
    }


}



type Node struct {
	Address    string
	BlockChain *BlockChain
	Nodes      map[string]bool
}

func (node *Node) SendBlockChain(address string) {
	fmt.Println("Sending blockchain to " + address)
	conn, err := net.Dial("tcp", address)
	if err != nil {
		fmt.Println(err)
		return
	}
	encoder := gob.NewEncoder(conn)
	err = encoder.Encode("ReceiveBlockChain," + node.Address)

	err = encoder.Encode(&node.BlockChain)
	err = conn.Close()
	if err != nil {
		fmt.Println(err)
		return
	}
	fmt.Println("Sending blockchain completed to " + address)
}


func (node *Node) ReceiveBlockChain(decoder *gob.Decoder) {
	fmt.Println("Recieving blockchain")
	var chain *BlockChain
	err := decoder.Decode(&chain)
	if err != nil {
		fmt.Println(err)
		return
	}

	node.BlockChain = chain

	fmt.Println("Received blockchain")
}



func (node *Node) VerifyBlock() {

}




func (node *Node) SendNodes(address string) {
	fmt.Println("Sending nodes")
	conn, err := net.Dial("tcp", address)
	if err != nil {
		fmt.Println(err)
		return
	}
	encoder := gob.NewEncoder(conn)

	err = encoder.Encode("ReceiveNodes," + node.Address)
	err = encoder.Encode(node.Nodes)
	err = conn.Close()
	if err != nil {
		fmt.Println(err)
		return
	}
	fmt.Println("Nodes Sent")
}
func (node *Node) ReceiveNodes( /*conn net.Conn*/ decoder *gob.Decoder) {
	fmt.Println("Receiving nodes")

	var nodes map[string]bool
	//fmt.Println("decode started in receive nodes")
	//decoder := gob.NewDecoder(conn)
	err := decoder.Decode(&nodes)
	if err != nil {
		fmt.Println(err)
		return
	}
	for n := range nodes {
		if n == node.Address {
			continue
		}
		node.AddNode(n)
	}
	//fmt.Println("decode successful in client receive nodes")
	
	fmt.Println("Receiving nodes completed by " + node.Address + "\n")
}
func (node *Node) AddNode(address string) {
	if node.Nodes == nil {
		node.Nodes = make(map[string]bool)
	}
	node.Nodes[address] = true
	//fmt.Println("no of nodes inside function: ")
	//fmt.Println(len(node.Nodes))

}
func (node *Node) FloodNodes() {
	fmt.Println("flooding nodes")
	for currentNode := range node.Nodes {
		node.SendNodes(currentNode)
	}
	fmt.Println("flooding nodes completed")
}
func (node *Node) FloodBlockChain() {
	fmt.Println("flooding blockchain")
	for currentNode := range node.Nodes {
		node.SendBlockChain(currentNode)
	}
	fmt.Println("flooding blockchain completed")
}
func (node *Node) HandleConnections(conn net.Conn) {
	decoder := gob.NewDecoder(conn)
	//fmt.Println("decode started in client handle connection")
	var message string
	err := decoder.Decode(&message)
	if err != nil {
		fmt.Println("error from client handle connection")
		fmt.Println(err)
		return
	}
	messageContents := strings.Split(message, ",")
	action := messageContents[0]
	sender := messageContents[1]



	switch action {
	case "ReceiveNodes":
		fmt.Println("The nodes from Bootstrap are recieved by " + node.Address)
		node.ReceiveNodes(decoder)
		fmt.Printf("\nThe neighbouring nodes of " + node.Address + " are ")
		fmt.Println(node.Nodes) //pritning nodes
	case "ReceiveBlockChain":
		node.ReceiveBlockChain(decoder)
	case "AddNode":
		node.AddNode(sender)
		node.SendBlockChain(sender)
		node.FloodNodes()
	}
	

}

func (node *Node) ListenConnections() {
	ln, err := net.Listen("tcp", node.Address)
	if err != nil {
		log.Fatal(err)
	}
	// fmt.Println("connection")
	for {
		conn, err := ln.Accept()
		if err != nil {
			fmt.Println("error from client listen connection")
			log.Println(err)
			return
		}
		fmt.Println("Connection accepted successfully") //after recieving nodes action
		go node.HandleConnections(conn)

	}

}


func (node *Node) NewTransactions(txs [][] string){

	// Adding new transactions

	fmt.Println(node)


	// node.BlockChain.AddBlock(txs)

	node.FloodBlockChain()

}





func (node *Node) HandleNewConnection(conn net.Conn, channel chan bool) {
	decoder := gob.NewDecoder(conn)

	var message string
	err := decoder.Decode(&message)
	if err != nil {
		fmt.Println("Error from client handle connection")
		fmt.Println(err)
		return
	}
	messageContents := strings.Split(message, ",")
	action := messageContents[0]
	if action != "AddNode" {
		fmt.Println("Incorrect Action")
		return
	}
	address := messageContents[1]

	fmt.Println("\nBootstrap connected to a new node: " + address + "\n")
	node.AddNode(address)


	fmt.Println("\nBootstrap is sending nodes information to the new node: " + address + "\n")
	node.SendNodes(address)

	fmt.Println("\nBootstrap is sending the BlockChain to the new node: " + address + "\n")
	
	node.SendBlockChain(address)
	
	//fmt.Println("no of nodes: ")
	//fmt.Println(len(node.Nodes))
	
	
	if len(node.Nodes) < 10 {
		channel <- false
	} else {
		defer connectionWait.Done()

		channel <- true
	}
	return
}

func (node *Node) ListenBootstrapConnection() {

	ln, err := net.Listen("tcp", node.Address)
	if err != nil {
		log.Fatal(err)
	}
	channel := make(chan bool)
	for {
		conn, err := ln.Accept()
		if err != nil {
			log.Println(err)
			return
		}
		go node.HandleNewConnection(conn, channel)
		if <-channel {
			break
		}
	}
	_ = ln.Close()

}

func (node *Node) ConnectWithBootstrapNode(address string) {
	fmt.Println(node.Address + " connecting with bootstrap")
	conn, err := net.Dial("tcp", address)
	if err != nil {
		fmt.Println(err)
		return
	}
	encoder := gob.NewEncoder(conn)

	err = encoder.Encode("AddNode," + node.Address)
	// err = encoder.Encode(node.Nodes)
	err = conn.Close()
	if err != nil {
		fmt.Println(err)
		return
	}
}

var wg sync.WaitGroup

var connectionWait sync.WaitGroup



