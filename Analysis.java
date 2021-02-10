import java.util.*;
import static java.util.stream.Collectors.*;

import java.io.FileOutputStream;
import java.io.ObjectOutputStream;
import java.io.*;
import org.antlr.v4.runtime.tree.ParseTreeProperty;
import org.antlr.v4.runtime.tree.TerminalNode;
import java.util.HashMap;
import java.lang.Math;

// FIXME: You should limit your implementation to this class. You are free to add new auxilliary classes. You do not need to touch the LoopNext.g4 file.
class Analysis extends LoopNestBaseListener {

    // Possible types
    enum Types {
        Byte, Short, Int, Long, Char, Float, Double, Boolean, String
    }

    // Type of variable declaration
    enum VariableType {
        Primitive, Array, Literal
    }

    // Types of caches supported
    enum CacheTypes {
        DirectMapped, SetAssociative, FullyAssociative,
    }

    // auxilliary data-structure for converting strings
    // to types, ignoring strings because string is not a
    // valid type for loop bounds
    final Map<String, Types> stringToType = Collections.unmodifiableMap(new HashMap<String, Types>() {
        private static final long serialVersionUID = 1L;

        {
            put("byte", Types.Byte);
            put("short", Types.Short);
            put("int", Types.Int);
            put("long", Types.Long);
            put("char", Types.Char);
            put("float", Types.Float);
            put("double", Types.Double);
            put("boolean", Types.Boolean);
        }
    });

    // auxilliary data-structure for mapping types to their byte-size
    // size x means the actual size is 2^x bytes, again ignoring strings
    final Map<Types, Integer> typeToSize = Collections.unmodifiableMap(new HashMap<Types, Integer>() {
        private static final long serialVersionUID = 1L;

        {
            put(Types.Byte, 0);
            put(Types.Short, 1);
            put(Types.Int, 2);
            put(Types.Long, 3);
            put(Types.Char, 1);
            put(Types.Float, 2);
            put(Types.Double, 3);
            put(Types.Boolean, 0);
        }
    });

    // Map of cache type string to value of CacheTypes
    final Map<String, CacheTypes> stringToCacheType = Collections.unmodifiableMap(new HashMap<String, CacheTypes>() {
        private static final long serialVersionUID = 1L;

        {
            put("FullyAssociative", CacheTypes.FullyAssociative);
            put("SetAssociative", CacheTypes.SetAssociative);
            put("DirectMapped", CacheTypes.DirectMapped);
        }
    });

    public Analysis() {
        
    }
    HashMap<String,String> variable;
    HashMap<String,Integer> loopLevel;
    HashMap<String,Long> cacheMiss;
    HashMap<String,Integer> strideForLoop;
    HashMap<String,String> arrayType;
    HashMap<String,Integer> arrayDimension;
    HashMap<String,Integer> arrayLoopLevel;
    HashMap<String,String> arrayIndex;
    HashMap<String,String> loopUpperBound;
    ArrayList<HashMap> result= new ArrayList<HashMap>();
    long cachePower, blockPower, wordPower, cacheSize, blockSize, wordSize;
    int n;
    int loopCount=0;
    int loopLevelCount=0;
    String loopNesting="";
    CacheTypes cache;
    


    // FIXME: Feel free to override additional methods from
    // LoopNestBaseListener.java based on your needs.
    // Method entry callback
    @Override
    public void enterMethodDeclaration(LoopNestParser.MethodDeclarationContext ctx) {
        //System.out.println("enterMethodDeclaration");
        variable= new HashMap<String,String>() ;
        loopLevel= new HashMap<String,Integer>();
        cacheMiss= new HashMap<String,Long>();
        strideForLoop= new HashMap<String,Integer>();
        arrayType = new HashMap<String,String>();
        arrayDimension = new HashMap<String,Integer>();
        arrayLoopLevel= new HashMap<String,Integer>();
        arrayIndex= new HashMap<String,String>();
        loopUpperBound= new HashMap<String,String>();
        loopCount=0;
        loopLevelCount=0;
        loopNesting="";
    }
    
    public void exitMethodBody(LoopNestParser.MethodBodyContext ctx){
    /*System.out.println("variables" + variable);
    System.out.println("array type" + arrayType);
    System.out.println("array index" + arrayIndex);
    System.out.println("array dimension" + arrayDimension);
    System.out.println("array loop level" + arrayLoopLevel);
    System.out.println("strides" + strideForLoop);
    System.out.println("loop bounds" + loopUpperBound);*/
    cachePower=Integer.parseInt(variable.get("cachePower"));
    blockPower=Integer.parseInt(variable.get("blockPower"));
    cacheSize=(long)Math.pow(2,cachePower);
    blockSize=(long)Math.pow(2,blockPower);
    n=Integer.parseInt(variable.get("N"));
    String x= variable.get("cacheType");
    cache= stringToCacheType.get(x.substring(1,x.length()-1));   
    for (Map.Entry element: arrayIndex.entrySet()){
         String arr=(String)element.getKey();
         String arrIndex=(String)element.getValue();
         if(arr!=null && arrIndex!=null)
            cacheMissCount(arr,arrIndex);
    }
    result.add(cacheMiss);
    }
    
    private void cacheMissCount(String arr, String arrIndex){
    wordPower=typeToSize.get(stringToType.get(arrayType.get(arr)));
    wordSize=(long)Math.pow(2,wordPower);
    int dimension= arrayDimension.get(arr);
    int loopLevelOfArray=arrayLoopLevel.get(arr);
    long totalMiss=1L;
    long arraySize= (long)Math.pow(n,dimension) * wordSize;
    long factor= arraySize/cacheSize; 
    long b=blockSize/wordSize;
    if(cache==CacheTypes.DirectMapped){ 
      if (loopCount==1){
         int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting)));
         int stride=strideForLoop.get(loopNesting);
            if(b>stride){
               totalMiss=loopBound/b;
            } 
            else
               totalMiss=loopBound/stride;       
      }
      else if(loopCount==2){
         if(loopCount==dimension){
             if(loopNesting.equals(arrIndex)){//array accessed in row major order
                long loopMiss=1L;
                int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                if(b>stride)
                   loopMiss= loopBound/b;
                else loopMiss= loopBound/stride;
                totalMiss*= loopMiss;
                stride=strideForLoop.get(loopNesting.substring(0,1));
                loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                loopMiss=loopBound/stride;
                totalMiss*= loopMiss;
             }
             else{//array accessed in column major order
               long loopMiss=1L;
               int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
               int stride=strideForLoop.get(loopNesting.substring(1,2)); 
               loopMiss=loopBound/stride;
               totalMiss*=loopMiss;
               loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
               stride=strideForLoop.get(loopNesting.substring(0,1)); 
               if(factor<=1){
                  if(b<stride)
                    loopMiss=loopBound/stride;
                  else
                    loopMiss=loopBound/b;
               }  
               else{
                  loopMiss=loopBound/stride;
               }
               totalMiss*=loopMiss;
             }
         }
         else{
             if(arrIndex.equals(loopNesting.substring(0,1))){//array index is at outer loop
               long loopMiss=1L;
               int stride=strideForLoop.get(loopNesting.substring(0,1));
               int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
               if(b>stride)
                   loopMiss= loopBound/b;
               else
                   loopMiss=loopBound/stride;
               totalMiss*=loopMiss;
             }
             else{//array index at inner loop
                long loopMiss=1L;
                int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                int stride=strideForLoop.get(loopNesting.substring(1,2));
                if(b>stride)
                   loopMiss=loopBound/b;
                else
                   loopMiss=loopBound/stride;
                totalMiss*=loopMiss;
                if(factor>1){
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;
                } 
             }
         }
      }
      else if(loopCount==3){
          if(dimension==1){
              if(arrayLoopLevel.get(arr)==1){
                  int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                  int stride=strideForLoop.get(loopNesting.substring(0,1));
                  if(b>stride)
                     totalMiss=loopBound/b;
                  else
                     totalMiss=loopBound/stride; 
                  }//array level==1
              else if(arrayLoopLevel.get(arr)==2){
                 if(arrIndex.equals(loopNesting.substring(0,1))){//array index is at outer loop
                    long loopMiss=1L;
                    int stride=strideForLoop.get(loopNesting.substring(0,1));
                    int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
                    if(b>stride)
                       loopMiss= loopBound/b;
                    else
                       loopMiss=loopBound/stride;
                    totalMiss*=loopMiss;
                 }
                 else{//array index at inner loop
                    long loopMiss=1L;
                    int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                    int stride=strideForLoop.get(loopNesting.substring(1,2));
                    if(b>stride)
                       loopMiss=loopBound/b;
                    else
                       loopMiss=loopBound/stride;
                    totalMiss*=loopMiss;
                    if(factor>1){
                       loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                       stride=strideForLoop.get(loopNesting.substring(0,1));
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                    } 
                 } 
              }
              else{//arraylevel=3
                  if(arrIndex.equals(loopNesting.substring(0,1))){//index of outermost loop matches
                      long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(0,1));
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else
                         loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                  }
                  else if(arrIndex.equals(loopNesting.substring(1,2))){//index matches for middle loop
                       long loopMiss=1L;
                       int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                       int stride=strideForLoop.get(loopNesting.substring(1,2));
                       if(b>stride)
                          loopMiss=loopBound/b;
                       else
                          loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                       if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                       }
                  }
                  else{//index matches for innermost loop
                       long loopMiss=1L;
                       int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                       int stride=strideForLoop.get(loopNesting.substring(2,3));
                       if(b>stride)
                          loopMiss=loopBound/b;
                       else
                          loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                       if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                          stride=strideForLoop.get(loopNesting.substring(1,2));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                       }
                  }
              }//arraylevel=3
          }
          else{// if(dimension==2)
              if(arrayLoopLevel.get(arr)==3){//array level=3 
                  String rowIndex= arrIndex.substring(0,1);
                  String colIndex=arrIndex.substring(1,2);
                  String l1= loopNesting.substring(0,1);
                  String l2= loopNesting.substring(1,2);
                  String l3= loopNesting.substring(2,3);
                  if(arrIndex.equals(loopNesting.substring(0,2))){//ijk ij
                      long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else 
                         loopMiss= loopBound/stride;
                      totalMiss*= loopMiss;
                      stride=strideForLoop.get(loopNesting.substring(0,1));
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      loopMiss=loopBound/stride;
                      totalMiss*= loopMiss;
                  }
                  else if(arrIndex.equals(loopNesting.substring(1,3))){//ijk jk
                      long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else 
                         loopMiss= loopBound/stride;
                      totalMiss*= loopMiss;
                      stride=strideForLoop.get(loopNesting.substring(0,1));
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      loopMiss=loopBound/stride;
                      totalMiss*= loopMiss; 
                      if(factor>1){
                         stride=strideForLoop.get(loopNesting.substring(0,1));
                         loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                         loopMiss=loopBound/stride;
                         totalMiss*=loopMiss;
                      }
                  }
                  else if(l2.equals(colIndex) && l3.equals(rowIndex)){//ijk kj
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                      stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      if(factor<=1){
                         if(b<stride)
                            loopMiss=loopBound/stride;
                         else
                            loopMiss=loopBound/b;               
                      }  
                      else{
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;         
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                      }
                      totalMiss*=loopMiss;
                      }
                 else if(l2.equals(rowIndex) && l1.equals(colIndex)){//ijk ji
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                      int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      stride=strideForLoop.get(loopNesting.substring(0,1)); 
                      if(factor<=1){
                          if(b<stride)
                             loopMiss=loopBound/stride;
                          else
                             loopMiss=loopBound/b;
                      }  
                      else{
                           loopMiss=loopBound/stride;
                      }
                      totalMiss*=loopMiss;
                  }
                  else if(l1.equals(rowIndex) && l3.equals(colIndex)){//ijk ik
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      if(b<stride)
                          loopMiss=loopBound/stride;
                      else
                          loopMiss=loopBound/b;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      stride=strideForLoop.get(loopNesting.substring(0,1)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                  }
                  else if(l3.equals(rowIndex) && l1.equals(colIndex)){//ijk ki
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                      if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                          stride=strideForLoop.get(loopNesting.substring(1,2)); 
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1)); 
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                      }
                      else{
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1)); 
                          loopMiss=loopBound/stride;
                          if(b<stride)
                             loopMiss=loopBound/stride;
                          else
                             loopMiss=loopBound/b;
                          totalMiss*=loopMiss;
                      }
                  }
              }
              else{//array level=2
                  if(arrIndex.equals(loopNesting.substring(0,2))){//array accessed in row major order
                     long loopMiss=1L;
                     int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                     int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                     if(b>stride)
                        loopMiss= loopBound/b;
                     else loopMiss= loopBound/stride;
                     totalMiss*= loopMiss;
                     stride=strideForLoop.get(loopNesting.substring(0,1));
                     loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                     loopMiss=loopBound/stride;
                     totalMiss*= loopMiss;
                 }
                 else{//array accessed in column major order
                     long loopMiss=1L;
                     int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                     int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                     loopMiss=loopBound/stride;
                     totalMiss*=loopMiss;
                     loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                     stride=strideForLoop.get(loopNesting.substring(0,1)); 
                     if(factor<=1){
                        if(b<stride)
                           loopMiss=loopBound/stride;
                        else
                          loopMiss=loopBound/b;
                     }  
                     else{
                        loopMiss=loopBound/stride;
                     }
                     totalMiss*=loopMiss;
                 }
              }
          }
       
      }//loopcount==3
      else{//loopcount==4
            if(dimension==1){
              if(arrayLoopLevel.get(arr)==1){
                  int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                  int stride=strideForLoop.get(loopNesting.substring(0,1));
                  if(b>stride)
                     totalMiss=loopBound/b;
                  else
                     totalMiss=loopBound/stride; 
                  }//array level==1
              else if(arrayLoopLevel.get(arr)==2){
                 if(arrIndex.equals(loopNesting.substring(0,1))){//array index is at outer loop
                    long loopMiss=1L;
                    int stride=strideForLoop.get(loopNesting.substring(0,1));
                    int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
                    if(b>stride)
                       loopMiss= loopBound/b;
                    else
                       loopMiss=loopBound/stride;
                    totalMiss*=loopMiss;
                 }
                 else{//array index at inner loop
                    long loopMiss=1L;
                    int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                    int stride=strideForLoop.get(loopNesting.substring(1,2));
                    if(b>stride)
                       loopMiss=loopBound/b;
                    else
                       loopMiss=loopBound/stride;
                    totalMiss*=loopMiss;
                    if(factor>1){
                       loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                       stride=strideForLoop.get(loopNesting.substring(0,1));
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                    } 
                 } 
              }
              else if (arrayLoopLevel.get(arr)==3){//arraylevel=3
                  if(arrIndex.equals(loopNesting.substring(0,1))){//index of outermost loop matches
                      long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(0,1));
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else
                         loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                  }
                  else if(arrIndex.equals(loopNesting.substring(1,2))){//index matches for middle loop
                       long loopMiss=1L;
                       int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                       int stride=strideForLoop.get(loopNesting.substring(1,2));
                       if(b>stride)
                          loopMiss=loopBound/b;
                       else
                          loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                       if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                       }
                  }
                  else{//index matches for innermost loop
                       long loopMiss=1L;
                       int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                       int stride=strideForLoop.get(loopNesting.substring(2,3));
                       if(b>stride)
                          loopMiss=loopBound/b;
                       else
                          loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                       if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                          stride=strideForLoop.get(loopNesting.substring(1,2));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                       }
                  }
              }//arraylevel=3
              else{
                  if(arrIndex.equals(loopNesting.substring(0,1))){
                        long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(0,1));
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else
                         loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;  
                  }
                  else if(arrIndex.equals(loopNesting.substring(1,2))){
                       long loopMiss=1L;
                    int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                    int stride=strideForLoop.get(loopNesting.substring(1,2));
                    if(b>stride)
                       loopMiss=loopBound/b;
                    else
                       loopMiss=loopBound/stride;
                    totalMiss*=loopMiss;
                    if(factor>1){
                       loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                       stride=strideForLoop.get(loopNesting.substring(0,1));
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                    }      
                  }
                  else if(arrIndex.equals(loopNesting.substring(2,3))){
                       long loopMiss=1L;
                       int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                       int stride=strideForLoop.get(loopNesting.substring(2,3));
                       if(b>stride)
                          loopMiss=loopBound/b;
                       else
                          loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                       if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                          stride=strideForLoop.get(loopNesting.substring(1,2));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                       }
                  }
                  else{
                       long loopMiss=1L;
                       int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(3,4))));
                       int stride=strideForLoop.get(loopNesting.substring(3,4));
                       if(b>stride)
                          loopMiss=loopBound/b;
                       else
                          loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                       if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                          stride=strideForLoop.get(loopNesting.substring(2,3));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                          stride=strideForLoop.get(loopNesting.substring(1,2));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                       }
                  }
              }
          }
          else{//dimension2
                if (arrayLoopLevel.get(arr)==2){//array level=2
                  if(arrIndex.equals(loopNesting.substring(0,2))){//array accessed in row major order
                     long loopMiss=1L;
                     int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                     int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                     if(b>stride)
                        loopMiss= loopBound/b;
                     else loopMiss= loopBound/stride;
                     totalMiss*= loopMiss;
                     stride=strideForLoop.get(loopNesting.substring(0,1));
                     loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                     loopMiss=loopBound/stride;
                     totalMiss*= loopMiss;
                 }
                 else{//array accessed in column major order
                     long loopMiss=1L;
                     int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                     int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                     loopMiss=loopBound/stride;
                     totalMiss*=loopMiss;
                     loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                     stride=strideForLoop.get(loopNesting.substring(0,1)); 
                     if(factor<=1){
                        if(b<stride)
                           loopMiss=loopBound/stride;
                        else
                          loopMiss=loopBound/b;
                     }  
                     else{
                        loopMiss=loopBound/stride;
                     }
                     totalMiss*=loopMiss;
                 }
              }
              else{//array level=3 
                  String rowIndex= arrIndex.substring(0,1);
                  String colIndex=arrIndex.substring(1,2);
                  String l1= loopNesting.substring(0,1);
                  String l2= loopNesting.substring(1,2);
                  String l3= loopNesting.substring(2,3);
                  if(arrIndex.equals(loopNesting.substring(0,2))){//ijk ij
                      long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else 
                         loopMiss= loopBound/stride;
                      totalMiss*= loopMiss;
                      stride=strideForLoop.get(loopNesting.substring(0,1));
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      loopMiss=loopBound/stride;
                      totalMiss*= loopMiss;
                  }
                  else if(arrIndex.equals(loopNesting.substring(1,3))){//ijk jk
                      long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else 
                         loopMiss= loopBound/stride;
                      totalMiss*= loopMiss;
                      stride=strideForLoop.get(loopNesting.substring(0,1));
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      loopMiss=loopBound/stride;
                      totalMiss*= loopMiss; 
                      if(factor>1){
                         stride=strideForLoop.get(loopNesting.substring(0,1));
                         loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                         loopMiss=loopBound/stride;
                         totalMiss*=loopMiss;
                      }
                  }
                  else if(l2.equals(colIndex) && l3.equals(rowIndex)){//ijk kj
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                      stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      if(factor<=1){
                         if(b<stride)
                            loopMiss=loopBound/stride;
                         else
                            loopMiss=loopBound/b;               
                      }  
                      else{
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;         
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                      }
                      totalMiss*=loopMiss;
                      }
                 else if(l2.equals(rowIndex) && l1.equals(colIndex)){//ijk ji
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                      int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      stride=strideForLoop.get(loopNesting.substring(0,1)); 
                      if(factor<=1){
                          if(b<stride)
                             loopMiss=loopBound/stride;
                          else
                             loopMiss=loopBound/b;
                      }  
                      else{
                           loopMiss=loopBound/stride;
                      }
                      totalMiss*=loopMiss;
                  }
                  else if(l1.equals(rowIndex) && l3.equals(colIndex)){//ijk ik
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      if(b<stride)
                          loopMiss=loopBound/stride;
                      else
                          loopMiss=loopBound/b;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      stride=strideForLoop.get(loopNesting.substring(0,1)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                  }
                  else if(l3.equals(rowIndex) && l1.equals(colIndex)){//ijk ki
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                      if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                          stride=strideForLoop.get(loopNesting.substring(1,2)); 
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1)); 
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                      }
                      else{
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1)); 
                          loopMiss=loopBound/stride;
                          if(b<stride)
                             loopMiss=loopBound/stride;
                          else
                             loopMiss=loopBound/b;
                          totalMiss*=loopMiss;
                      }
                  }
              }
              
          }//dimension==2
      }//loop count ==4
    }//direct mapped
    else if(cache==CacheTypes.FullyAssociative){
        if (loopCount==1){
         int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting)));
         int stride=strideForLoop.get(loopNesting);
            if(b>stride){
               totalMiss=loopBound/b;
            } 
            else
               totalMiss=loopBound/stride;       
        }
        else if(loopCount==2){
           if(loopCount!=dimension){
               if(arrIndex.equals(loopNesting.substring(0,1))){//array index is at outer loop
               long loopMiss=1L;
               int stride=strideForLoop.get(loopNesting.substring(0,1));
               int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
               if(b>stride)
                   loopMiss= loopBound/b;
               else
                   loopMiss=loopBound/stride;
               totalMiss*=loopMiss;
             }
             else{//array index at inner loop
                long loopMiss=1L;
                int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                int stride=strideForLoop.get(loopNesting.substring(1,2));
                if(b>stride)
                   loopMiss=loopBound/b;
                else
                   loopMiss=loopBound/stride;
                totalMiss*=loopMiss;
                long cacheOccupied=loopMiss*blockSize;
                if(cacheOccupied>cacheSize){
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;}
              }
            }
 
             else{  //start dim==loopnest
                if(loopNesting.equals(arrIndex)){//array accessed in row major order
                  long loopMiss=1L;
                  int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                  int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                  if(b>stride)
                     loopMiss= loopBound/b;
                  else
                     loopMiss= loopBound/stride;
                  totalMiss*= loopMiss;
                  stride=strideForLoop.get(loopNesting.substring(0,1));
                  loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                  loopMiss=loopBound/stride;
                  totalMiss*= loopMiss;
                  }
                else{//2array accessed in col major order
                   long loopMiss=1L;
                   int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                   int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   long cacheOccupied=loopMiss*blockSize;
                   if(cacheOccupied>cacheSize)
                       loopMiss=loopBound/stride;
                   else{
                       if(b<stride)
                         loopMiss=loopBound/stride;
                       else
                         loopMiss=loopBound/b;
                   }
                   totalMiss*=loopMiss;
                }//2
           }//end dim==loopnest
        }//end loopcount2
        else{// loopCount==3
            if(dimension==1){
                if(arrayLoopLevel.get(arr)==1){
                     long loopMiss=1L;
                     int stride=strideForLoop.get(loopNesting.substring(0,1));
                     int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
                     if(b>stride)
                        loopMiss= loopBound/b;
                     else
                        loopMiss=loopBound/stride;
                     totalMiss*=loopMiss;
                }
                else if(arrayLoopLevel.get(arr)==2){
                     if(arrIndex.equals(loopNesting.substring(0,1))){//array index is at outer loop
                         long loopMiss=1L;
                         int stride=strideForLoop.get(loopNesting.substring(0,1));
                         int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
                         if(b>stride)
                              loopMiss= loopBound/b;
                         else
                              loopMiss=loopBound/stride;
                         totalMiss*=loopMiss;
                     }
                     else{//array index at inner loop
                        long loopMiss=1L;
                        int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                        int stride=strideForLoop.get(loopNesting.substring(1,2));
                        if(b>stride)
                            loopMiss=loopBound/b;
                        else
                            loopMiss=loopBound/stride;
                        totalMiss*=loopMiss;
                        long cacheOccupied=loopMiss*blockSize;
                        if(cacheOccupied>cacheSize){
                           loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                           stride=strideForLoop.get(loopNesting.substring(0,1));
                           loopMiss=loopBound/stride;
                           totalMiss*=loopMiss;
                        }
                    }
                }
                else{// array level 3
                     if(arrIndex.equals(loopNesting.substring(0,1))){//array index is at outer loop ijk i
                         long loopMiss=1L;
                         int stride=strideForLoop.get(loopNesting.substring(0,1));
                         int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
                         if(b>stride)
                              loopMiss= loopBound/b;
                         else
                              loopMiss=loopBound/stride;
                         totalMiss*=loopMiss;
                     }
                     else if(arrIndex.equals(loopNesting.substring(1,2))){//ijk j
                        long loopMiss=1L;
                        int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                        int stride=strideForLoop.get(loopNesting.substring(1,2));
                        if(b>stride)
                            loopMiss=loopBound/b;
                        else
                            loopMiss=loopBound/stride;
                        totalMiss*=loopMiss;
                        long cacheOccupied=loopMiss*blockSize;
                        if(cacheOccupied>cacheSize){
                           loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                           stride=strideForLoop.get(loopNesting.substring(0,1));
                           loopMiss=loopBound/stride;
                           totalMiss*=loopMiss;
                        }
                    }
                     else{// ijk k
                        long loopMiss=1L;
                        int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                        int stride=strideForLoop.get(loopNesting.substring(2,3));
                        if(b>stride)
                            loopMiss=loopBound/b;
                        else
                            loopMiss=loopBound/stride;
                        totalMiss*=loopMiss;
                        long cacheOccupied=loopMiss*blockSize;
                        if(cacheOccupied>cacheSize){//1
                           loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                           stride=strideForLoop.get(loopNesting.substring(1,2));
                           loopMiss=loopBound/stride;
                           totalMiss*=loopMiss;
                           loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                           stride=strideForLoop.get(loopNesting.substring(0,1));
                           loopMiss=loopBound/stride;
                           totalMiss*=loopMiss; 
                    }//1
                }//ijk k
             }
           }
            else{// dimension=2
                if(arrayLoopLevel.get(arr)==2){// array level 2
                  if(arrIndex.equals(loopNesting.substring(0,2))){//array accessed in row major order
                      long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else
                        loopMiss= loopBound/stride;
                      totalMiss*= loopMiss;
                      stride=strideForLoop.get(loopNesting.substring(0,1));
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      loopMiss=loopBound/stride;
                      totalMiss*= loopMiss;
                  }
                  else{//2array accessed in col major order
                    long loopMiss=1L;
                    int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                    int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                    loopMiss=loopBound/stride;
                    totalMiss*=loopMiss;
                    loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                    stride=strideForLoop.get(loopNesting.substring(0,1));
                    long cacheOccupied=loopMiss*blockSize;
                    if(cacheOccupied>cacheSize)
                        loopMiss=loopBound/stride;
                    else{
                        if(b<stride)
                           loopMiss=loopBound/stride;
                        else
                           loopMiss=loopBound/b;
                    }
                    totalMiss*=loopMiss;
                 }//2
                
                }
                else{// array level 3
                  String rowIndex= arrIndex.substring(0,1);
                  String colIndex=arrIndex.substring(1,2);
                  String l1= loopNesting.substring(0,1);
                  String l2= loopNesting.substring(1,2);
                  String l3= loopNesting.substring(2,3);
                  if(arrIndex.equals(loopNesting.substring(0,2))){//ijk ij
                  //array accessed in row major order
                  long loopMiss=1L;
                  int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                  int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                  if(b>stride)
                     loopMiss= loopBound/b;
                  else
                     loopMiss= loopBound/stride;
                  totalMiss*= loopMiss;
                  stride=strideForLoop.get(loopNesting.substring(0,1));
                  loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                  loopMiss=loopBound/stride;
                  totalMiss*= loopMiss;
               
                  }
                   else if(arrIndex.equals(loopNesting.substring(1,3))){//ijk jk
                  long loopMiss=1L;
                  int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                  int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3)))); 
                  if(b>stride)
                     loopMiss= loopBound/b;
                  else
                     loopMiss= loopBound/stride;
                  totalMiss*= loopMiss;
                  stride=strideForLoop.get(loopNesting.substring(1,2));
                  loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                  loopMiss=loopBound/stride;
                  totalMiss*= loopMiss;
                   long cacheOccupied=totalMiss*blockSize;
                    if(cacheOccupied>cacheSize){
                         stride=strideForLoop.get(loopNesting.substring(0,1));
                         loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                         loopMiss=loopBound/stride;
                         totalMiss*= loopMiss; 
                    }
                  }
                  else if(l2.equals(colIndex) && l3.equals(rowIndex)){//ijk kj
                   long loopMiss=1L;
                   int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                   int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                   stride=strideForLoop.get(loopNesting.substring(1,2));
                   long cacheOccupied=loopMiss*blockSize;
                   if(cacheOccupied>cacheSize){
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                       loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                       stride=strideForLoop.get(loopNesting.substring(0,1)); 
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                   }
                   else{
                       if(b<stride)
                         loopMiss=loopBound/stride;
                       else
                         loopMiss=loopBound/b;
                         totalMiss*=loopMiss;
                         long y= totalMiss*blockSize;
                         if(y>cacheSize){
                           loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                           stride=strideForLoop.get(loopNesting.substring(0,1)); 
                           loopMiss=loopBound/stride;
                           totalMiss*=loopMiss;
                         }
                   }                     
                  }
                  else if(l2.equals(rowIndex) && l1.equals(colIndex)){//ijk ji
                   long loopMiss=1L;
                   int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                   int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   long cacheOccupied=loopMiss*blockSize;
                   if(cacheOccupied>cacheSize)
                       loopMiss=loopBound/stride;
                   else{
                       if(b<stride)
                         loopMiss=loopBound/stride;
                       else
                         loopMiss=loopBound/b;
                   }
                   totalMiss*=loopMiss;
                  }
                  else if(l1.equals(rowIndex) && l3.equals(colIndex)){//ijk ik
                   long loopMiss=1L;
                   int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                   int stride=strideForLoop.get(loopNesting.substring(2,3));
                     if(b<stride)
                         loopMiss=loopBound/stride;
                       else
                         loopMiss=loopBound/b;
                       totalMiss*=loopMiss;
                     long cacheOccupied=loopMiss*blockSize;
                     if(cacheOccupied>cacheSize){
                         loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                       stride=strideForLoop.get(loopNesting.substring(1,2));
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                     }
                       loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                       stride=strideForLoop.get(loopNesting.substring(0,1));
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                  }
                  else if(l3.equals(rowIndex) && l1.equals(colIndex)){//ijk ki
                   long loopMiss=1L;
                   int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                   int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;
                   long cacheOccupied=loopMiss*blockSize;
                   if(cacheOccupied>cacheSize){
                       loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                       stride=strideForLoop.get(loopNesting.substring(1,2));
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;
                       loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                       stride=strideForLoop.get(loopNesting.substring(0,1));
                       loopMiss=loopBound/stride;
                       totalMiss*=loopMiss;}
                   else{
                       loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                       stride=strideForLoop.get(loopNesting.substring(0,1));
                       if(b<stride)
                         loopMiss=loopBound/stride;
                       else
                         loopMiss=loopBound/b;
                       totalMiss*=loopMiss;
                   }
                  }
                }
            }
        }//loopcount 3
    }//end fully ass
    else if(cache==CacheTypes.SetAssociative){
        int setSize=1;
        if(variable.get("setSize")!=null)
              setSize=Integer.parseInt(variable.get("setSize"));
        if(loopCount==1){
           int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting)));
           int stride=strideForLoop.get(loopNesting);
           if(b>stride){
               totalMiss=loopBound/b;
            } 
            else
               totalMiss=loopBound/stride;     
        }
        else if(loopCount==2){
           long blocks= cacheSize/blockSize;
           int setCount= (int)(blocks/setSize);
           int[] setFull= new int[setCount];
           for (int i=0;i<setCount;i++)
               setFull[i]=0;
           if(loopCount!=dimension){
               if(arrIndex.equals(loopNesting.substring(0,1))){//array index is at outer loop
               long loopMiss=1L;
               int stride=strideForLoop.get(loopNesting.substring(0,1));
               int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
               if(b>stride)
                   loopMiss= loopBound/b;
               else
                   loopMiss=loopBound/stride;
               totalMiss*=loopMiss;
               }//end if
            else{  
                long loopMiss=1L;
                int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                int stride=strideForLoop.get(loopNesting.substring(1,2));
                if(b>stride)
                   loopMiss=loopBound/b;
                else
                   loopMiss=loopBound/stride;
                totalMiss*=loopMiss;
                if(factor>1){
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;} 

            }//end else
            }//end loop!=dim
            else{//loop==dim
                if(loopNesting.equals(arrIndex)){//array accessed in row major order
                   long loopMiss=1L;
                   int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                   int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                   if(b>stride)
                      loopMiss= loopBound/b;
                   else loopMiss= loopBound/stride;
                   totalMiss*= loopMiss;
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   loopMiss=loopBound/stride;
                   totalMiss*= loopMiss;
                }
                else{
                    long loopMiss=1L;
                   int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                   int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                   if(b>stride)
                      loopMiss= loopBound/b;
                   else loopMiss= loopBound/stride;
                   totalMiss*= loopMiss;
                   if(factor>1){
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;} 
                }
            }//end loop==dim
        }//end loopcount2
        else{//loopCount==3
           long blocks= cacheSize/blockSize;
           int setCount= (int)(blocks/setSize);
           int[] setFull= new int[setCount];
           for (int i=0;i<setCount;i++)
               setFull[i]=0;
           if(dimension==1){
               if(arrIndex.equals(loopNesting.substring(0,1))){//array index is at outer loop
               long loopMiss=1L;
               int stride=strideForLoop.get(loopNesting.substring(0,1));
               int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1)))); 
               if(b>stride)
                   loopMiss= loopBound/b;
               else
                   loopMiss=loopBound/stride;
               totalMiss*=loopMiss;
               }//end if
            else if(arrIndex.equals(loopNesting.substring(1,2))){  
                long loopMiss=1L;
                int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                int stride=strideForLoop.get(loopNesting.substring(1,2));
                if(b>stride)
                   loopMiss=loopBound/b;
                else
                   loopMiss=loopBound/stride;
                totalMiss*=loopMiss;
                if(factor>1){
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;} 
            }//end else
            else{
                long loopMiss=1L;
                int loopBound=Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                int stride=strideForLoop.get(loopNesting.substring(2,3));
                if(b>stride)
                   loopMiss=loopBound/b;
                else
                   loopMiss=loopBound/stride;
                totalMiss*=loopMiss;
                if(factor>1){
                    loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                   stride=strideForLoop.get(loopNesting.substring(1,2));
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;
                   loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                   stride=strideForLoop.get(loopNesting.substring(0,1));
                   loopMiss=loopBound/stride;
                   totalMiss*=loopMiss;} 
           }
           }
           else{//dimension==2
                 String rowIndex= arrIndex.substring(0,1);
                  String colIndex=arrIndex.substring(1,2);
                  String l1= loopNesting.substring(0,1);
                  String l2= loopNesting.substring(1,2);
                  String l3= loopNesting.substring(2,3);
                  if(arrIndex.equals(loopNesting.substring(0,2))){// ijk ij 
                       long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else 
                         loopMiss= loopBound/stride;
                      totalMiss*= loopMiss;
                      stride=strideForLoop.get(loopNesting.substring(0,1));
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      loopMiss=loopBound/stride;
                      totalMiss*= loopMiss; 
                  }
                  else if(arrIndex.equals(loopNesting.substring(1,3))){//ijk jk
                       long loopMiss=1L;
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3)))); 
                      if(b>stride)
                         loopMiss= loopBound/b;
                      else 
                         loopMiss= loopBound/stride;
                      totalMiss*= loopMiss;
                      stride=strideForLoop.get(loopNesting.substring(1,2));
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                      loopMiss=loopBound/stride;
                      totalMiss*= loopMiss;
                        if(factor>1){
                         stride=strideForLoop.get(loopNesting.substring(0,1));
                         loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                         loopMiss=loopBound/stride;
                         totalMiss*=loopMiss;
                      }
                  }
                  else if(l2.equals(colIndex) && l3.equals(rowIndex)){// ijk kj
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                      stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      if(factor<=1){
                         if(b<stride)
                            loopMiss=loopBound/stride;
                         else
                            loopMiss=loopBound/b;               
                      }  
                      else{
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;         
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1));
                          loopMiss=loopBound/stride;
                      }
                      totalMiss*=loopMiss;
                  }
                  else if(l2.equals(rowIndex) && l1.equals(colIndex)){// ijk ji
                       long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                      int stride=strideForLoop.get(loopNesting.substring(1,2)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      stride=strideForLoop.get(loopNesting.substring(0,1)); 
                      if(factor<=1){
                         if(b<stride)
                            loopMiss=loopBound/stride;
                         else
                            loopMiss=loopBound/b;               
                      }  
                      else{
                       loopMiss=loopBound/stride;
                      }
                      totalMiss*=loopMiss;
                   }
                  else if(l1.equals(rowIndex) && l3.equals(colIndex)){//ijk ik
                       long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      if(b<stride)
                          loopMiss=loopBound/stride;
                      else
                          loopMiss=loopBound/b;
                      totalMiss*=loopMiss;
                      loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                      stride=strideForLoop.get(loopNesting.substring(0,1)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss; 
                  }
                  else if(l3.equals(rowIndex) && l1.equals(colIndex)){// ijk ki
                      long loopMiss=1L;
                      int loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(2,3))));
                      int stride=strideForLoop.get(loopNesting.substring(2,3)); 
                      loopMiss=loopBound/stride;
                      totalMiss*=loopMiss;
                        if(factor>1){
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(1,2))));
                          stride=strideForLoop.get(loopNesting.substring(1,2)); 
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1)); 
                          loopMiss=loopBound/stride;
                          totalMiss*=loopMiss;
                      }
                      else{
                          loopBound= Integer.parseInt(variable.get(loopUpperBound.get(loopNesting.substring(0,1))));
                          stride=strideForLoop.get(loopNesting.substring(0,1)); 
                          loopMiss=loopBound/stride;
                          if(b<stride)
                             loopMiss=loopBound/stride;
                          else
                             loopMiss=loopBound/b;
                          totalMiss*=loopMiss;
                      }
                  }
           }
        }
    }//end setAsso
    cacheMiss.put(arr,totalMiss);
    }//end cachemiss
    // End of testcase
    @Override
    public void exitMethodDeclarator(LoopNestParser.MethodDeclaratorContext ctx) {
        //System.out.println("exitMethodDeclarator");
    }
    @Override
    public void enterTests(LoopNestParser.TestsContext ctx){
       
    }
    @Override
    public void exitTests(LoopNestParser.TestsContext ctx) {
        System.out.println(result);
        try {
            FileOutputStream fos = new FileOutputStream("Results.obj");
            ObjectOutputStream oos = new ObjectOutputStream(fos);
            // FIXME: Serialize your data to a file
            // oos.writeObject();
            oos.writeObject(result);
            oos.close();
        } catch (Exception e) {
            throw new RuntimeException(e.getMessage());
        }
    }

    @Override 
    public void enterLocalVariableDeclarationStatement(LoopNestParser.LocalVariableDeclarationStatementContext ctx) 
   { 
      LoopNestParser.LocalVariableDeclarationContext varctx= ctx.localVariableDeclaration();
      if( varctx.unannType()!=null){
         if(varctx.unannType().unannArrayType()!=null){
            arrayType.put(varctx.variableDeclarator().variableDeclaratorId().getText(),varctx.unannType().unannArrayType().unannPrimitiveType().getText());
            arrayDimension.put(varctx.variableDeclarator().variableDeclaratorId().getText(),varctx.unannType().unannArrayType().dims().getText().length()/2);
         }  
         else{
            variable.put(varctx.variableDeclarator().variableDeclaratorId().getText(),varctx.variableDeclarator().literal().getText());
         }
      }
      else{
         variable.put(varctx.variableDeclarator().variableDeclaratorId().getText(),varctx.variableDeclarator().literal().getText());
      }
    }
 
    @Override 
    public void enterForStatement(LoopNestParser.ForStatementContext ctx) { 
      loopCount+=1;
      loopLevelCount+=1;
      loopLevel.put(ctx.forCondition().relationalExpression().expressionName(0).getText(),loopLevelCount);
      strideForLoop.put(ctx.forCondition().relationalExpression().expressionName(0).getText(),Integer.parseInt(ctx.forUpdate().simplifiedAssignment().
IntegerLiteral().getText()));  
      loopUpperBound.put(ctx.forCondition().relationalExpression().expressionName(0).getText(),ctx.forCondition().relationalExpression().expressionName(1).
Identifier().getText()); 
      loopNesting+= ctx.forCondition().relationalExpression().expressionName(0).getText();
    }

    @Override 
    public void exitForStatement(LoopNestParser.ForStatementContext ctx){
        loopLevelCount--;
    }

    @Override
    public void enterArrayAccess(LoopNestParser.ArrayAccessContext ctx){
        String arr="";
        for(LoopNestParser.ExpressionNameContext x:ctx.expressionName()){
            arr= arr + x.getText();
        }
        arrayLoopLevel.put(arr.substring(0,1),loopCount);
        arrayIndex.put(arr.substring(0,1),arr.substring(1));
    }

    @Override
    public void enterArrayAccess_lfno_primary(LoopNestParser.ArrayAccess_lfno_primaryContext ctx){
       String arr="";
        for(LoopNestParser.ExpressionNameContext x:ctx.expressionName()){
            arr= arr + x.getText();
        }
        arrayLoopLevel.put(arr.substring(0,1),loopCount);
        arrayIndex.put(arr.substring(0,1),arr.substring(1)); 
    }
    @Override
    public void exitLocalVariableDeclaration(LoopNestParser.LocalVariableDeclarationContext ctx) {

    }

    @Override
    public void exitVariableDeclarator(LoopNestParser.VariableDeclaratorContext ctx) {
    }

    @Override
    public void exitArrayCreationExpression(LoopNestParser.ArrayCreationExpressionContext ctx) {
    }

    @Override
    public void exitDimExprs(LoopNestParser.DimExprsContext ctx) {
    }

    @Override
    public void exitDimExpr(LoopNestParser.DimExprContext ctx) {
    }

    @Override
    public void exitLiteral(LoopNestParser.LiteralContext ctx) {
    }

    @Override
    public void exitVariableDeclaratorId(LoopNestParser.VariableDeclaratorIdContext ctx) {
    }

    @Override
    public void exitUnannArrayType(LoopNestParser.UnannArrayTypeContext ctx) {
    }

    @Override
    public void enterDims(LoopNestParser.DimsContext ctx) {
    }

    @Override
    public void exitUnannPrimitiveType(LoopNestParser.UnannPrimitiveTypeContext ctx) {
    }

    @Override
    public void exitNumericType(LoopNestParser.NumericTypeContext ctx) {
    }

    @Override
    public void exitIntegralType(LoopNestParser.IntegralTypeContext ctx) {
    }

    @Override
    public void exitFloatingPointType(LoopNestParser.FloatingPointTypeContext ctx) {
    }

    @Override
    public void exitForInit(LoopNestParser.ForInitContext ctx) {
    }

    @Override
    public void exitForCondition(LoopNestParser.ForConditionContext ctx) {
    }

    @Override
    public void exitRelationalExpression(LoopNestParser.RelationalExpressionContext ctx) {
    }

    @Override
    public void exitForUpdate(LoopNestParser.ForUpdateContext ctx) {
    }

    @Override
    public void exitSimplifiedAssignment(LoopNestParser.SimplifiedAssignmentContext ctx) {
    }

    @Override
    public void exitArrayAccess(LoopNestParser.ArrayAccessContext ctx) {
    }

    @Override
    public void exitArrayAccess_lfno_primary(LoopNestParser.ArrayAccess_lfno_primaryContext ctx) {

    }

}
