import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;


public class inference {
	private HashMap<String, ArrayList<String>> knowledgeBase = new HashMap<>();
	private HashMap<String, ArrayList<String>> groundTerms = new HashMap<>();
	
	inference(List<String> kb){
		ListIterator<String> li = kb.listIterator();
		while(li.hasNext()){
			String query = li.next().trim();
			if(query.contains("=>")){
				String[] rules = query.split("=>");
				ArrayList<String> entries = new ArrayList<>();
				String ruleName = rules[1].substring(0, rules[1].indexOf('(')).trim();
				if(knowledgeBase.containsKey(ruleName)){
					entries = knowledgeBase.get(ruleName);
				}
				entries.add(query);
				knowledgeBase.put(rules[1].substring(0, rules[1].indexOf('(')).trim(),entries);
			}else{
				ArrayList<String> entries = new ArrayList<>();
				String fact = query.substring(0, query.indexOf('(')).trim();
				if(groundTerms.containsKey(fact)){
					entries = groundTerms.get(fact);
				}
		
				entries.add(query);
				groundTerms.put(fact,entries);
			}
		}
	}
	
	public HashMap<String, String> UNIFY_VAR(String[] x, String[] y, HashMap<String, String> theta){
		if(theta.containsKey(x[0])){
			return UNIFY(new String[]{theta.get(x[0])}, y, theta);
		}else if(theta.containsKey(y[0])){
			return UNIFY(x, new String[]{theta.get(y[0])}, theta);
		}else{
			if(Character.isLowerCase(y[0].charAt(0)) == false){
				theta.put(x[0], y[0]);
			}	
			return theta;
		}
	}
	
	public HashMap<String, String> UNIFY(String[] x, String[] y, HashMap<String, String> theta){
		if(theta.get("failure").equals("true")){
			return theta;
		}else if(x.length == 1 && y.length == 1){
			if(x[0].equals(y[0])){
				return theta;
			}else if(Character.isLowerCase(x[0].charAt(0))){
				return UNIFY_VAR(new String[]{x[0]}, new String[]{y[0]}, theta);
			}else if(Character.isLowerCase(y[0].charAt(0))){
				return theta;
			}else{
				theta.replace("failure", "false", "true");
				return theta;
			}
		}else if(x.length != y.length){
			theta.replace("failure", "false", "true");
			return theta;
		}else{
			String[] temp1 = new String[x.length-1];
			String[] temp2 = new String[y.length-1];
			System.arraycopy(x, 1, temp1, 0, x.length-1);
			System.arraycopy(y, 1, temp2, 0, y.length-1);
			return UNIFY(temp1, temp2,(UNIFY(new String[]{x[0]}, new String[]{y[0]}, theta)));
		}
	}
	
	public String SUBSTITUTE(String goals, HashMap<String, String> theta){
		String[] arguments = goals.substring(goals.indexOf('(')+1, goals.indexOf(')')).split(",");
		for(int i = 0; i < arguments.length; i++){
			if(Character.isLowerCase(arguments[i].charAt(0)) && theta.containsKey(arguments[i])){
					arguments[i] = theta.get(arguments[i]);
			}
		}
		String newGoal = goals.substring(0,goals.indexOf('(')+1);
		newGoal = newGoal.concat(arguments[0]);
		for(int j = 1; j < arguments.length; j++){
			newGoal = newGoal.concat(",");
			newGoal = newGoal.concat(arguments[j]);
		}
		return newGoal.concat(")");
	}
	
	public ArrayList<HashMap<String, String>> FOL_BC_AND(String[] goals, HashMap<String, String> theta, ArrayList<String> loopDetect){
		ArrayList<HashMap<String, String>> theta_gen = new ArrayList<HashMap<String, String>>();
		if(theta.get("failure").equals("true")){
			theta_gen.add(theta);
			return theta_gen;
		}else if(goals.length == 0){
			theta_gen.add(theta);
			return theta_gen;
		}else{
			String[] rest = new String[goals.length-1];
			System.arraycopy(goals, 1, rest, 0, goals.length-1);
			
			ArrayList<HashMap<String, String>> theta1_gen = FOL_BC_OR(SUBSTITUTE(goals[0], theta),theta, loopDetect);
			ListIterator<HashMap<String, String>> itr = theta1_gen.listIterator();
			while(itr.hasNext()){	
				
				ArrayList<HashMap<String, String>> list_gen = FOL_BC_AND(rest, itr.next(), loopDetect);
				ListIterator<HashMap<String, String>> itr_gen = list_gen.listIterator();
				while(itr_gen.hasNext()){
					theta_gen.add(itr_gen.next());
				}
			}
			return theta_gen;
		}
	}
	
	public ArrayList<HashMap<String, String>> FOL_BC_OR(String query, HashMap<String, String> theta, ArrayList<String> loops){
		
		ArrayList<HashMap<String, String>> theta_gen = new ArrayList<>();
		if(groundTerms.containsKey(query.substring(0, query.indexOf('(')).trim())){
			ArrayList<String> facts = groundTerms.get(query.substring(0,query.indexOf('(')).trim());
			ListIterator<String> li = facts.listIterator();
			while(li.hasNext()){
				ArrayList<String> loopDetect = new ArrayList<String>(loops);
				String fact = li.next().trim();
				if(loopDetect.contains(fact) == false){
					loopDetect.add(fact);
					if(fact.trim().equals(query.trim())){
						theta_gen.add(theta);
					}else{
						HashMap<String, String> theta1 = new HashMap<String, String>();
						theta1.put("failure", "false");
						HashMap<String, String> temp = new HashMap<String, String>(UNIFY(query.substring(query.indexOf('(')+1, query.indexOf(')')).split(","), fact.substring(fact.indexOf('(')+1, fact.indexOf(')')).split(","), theta1));
						
						ArrayList<HashMap<String, String>> theta1_gen = FOL_BC_AND(new String[]{}, temp, loopDetect);
						ListIterator<HashMap<String, String>> itr_gen = theta1_gen.listIterator();
						while(itr_gen.hasNext()){
							HashMap<String, String> thetaList = itr_gen.next();
							if(thetaList.get("failure").equals("false")){
								Iterator<Map.Entry<String, String>> itr = theta.entrySet().iterator();
								while(itr.hasNext()){
									Map.Entry<String, String> val = itr.next();
									if(thetaList.containsKey(val.getKey()) == false){
										thetaList.put(val.getKey(), val.getValue());
									}
								}
								theta_gen.add(thetaList);
							}
						}
					}
				}
			}
		}
		if(knowledgeBase.containsKey(query.substring(0, query.indexOf('(')).trim())){
			ArrayList<String> rules = knowledgeBase.get(query.substring(0, query.indexOf('(')).trim());
			ListIterator<String> li = rules.listIterator();
			while(li.hasNext()){
				ArrayList<String> loopDetect = new ArrayList<String>(loops);
				String rule = li.next().trim();
				if(loopDetect.contains(rule) == false){
					loopDetect.add(rule);
					String[] ruleParts = rule.split("=>");
					HashMap<String, String> theta1 = new HashMap<String, String>();
					theta1.put("failure", "false");		
					String[] parent =  query.substring(query.indexOf('(')+1, query.indexOf(')')).split(",");
					String[] child = ruleParts[1].substring(ruleParts[1].indexOf('(')+1, ruleParts[1].indexOf(')')).split(",");
					ArrayList<HashMap<String, String>> theta1_gen = FOL_BC_AND(ruleParts[0].split("\\^"), UNIFY(ruleParts[1].substring(ruleParts[1].indexOf('(')+1, ruleParts[1].indexOf(')')).split(","), query.substring(query.indexOf('(')+1, query.indexOf(')')).split(","), theta1), loopDetect);
					ListIterator<HashMap<String, String>> itr_gen = theta1_gen.listIterator();
					while(itr_gen.hasNext()){
						HashMap<String, String> thetaList = itr_gen.next();
						if(thetaList.get("failure").equals("false")){
							HashMap<String, String> thetaTemp = new HashMap<String, String>(theta);
							for(int i = 0; i < parent.length; i++){
								if(Character.isLowerCase(parent[i].charAt(0))){
									if(thetaTemp.containsKey(parent[i])){
										if(Character.isLowerCase(child[i].charAt(0))){
											if(thetaList.get(child[i]).equals(thetaTemp.get(parent[i])) == false){
												thetaTemp.replace("failure", "false", "true");
											}
										}else{
											if(thetaTemp.get(parent[i]).equals(child[i]) == false){
												thetaTemp.replace("failure", "false", "true");
											}
										}
									}else{
										if(Character.isLowerCase(child[i].charAt(0))){
											if(thetaList.containsKey(child[i])){
											thetaTemp.put(parent[i], thetaList.get(child[i]));
											}
										}else{
											thetaTemp.put(parent[i], child[i]);
										}
									}
								}
							}
							theta_gen.add(thetaTemp);
						}
					}
				}
			}
		}
		if(theta_gen.isEmpty()){
			theta.replace("failure", "false", "true");
			theta_gen.add(theta);
		}
		return theta_gen;
	}
	
	public ArrayList<HashMap<String,String>> FOL_BC_ASK(String query){
		HashMap<String, String> theta = new HashMap<String, String>();
		theta.put("failure", "false");
		ArrayList<String> loopDetect = new ArrayList<String>();
		
		return FOL_BC_OR(query, theta, loopDetect);
	}
	
	public static void main(String args[]){
		try(Scanner sc = new Scanner(new BufferedReader(new FileReader(args[1])))){
			PrintWriter writer = new PrintWriter("output.txt", "UTF-8");
			List<String> queries = new ArrayList<String>();
			int n = Integer.parseInt(sc.nextLine());
			int count = 0;
			while(count < n){
				queries.add(sc.nextLine());
				count++;
			}
			int m = Integer.parseInt(sc.nextLine());
			count = 0;
			List<String> kb = new ArrayList<String>();
			
			while(count < m){
				kb.add(sc.nextLine());
				count++;
			}
			inference inf = new inference(kb);
			ListIterator<String> queryIte = queries.listIterator();
			while(queryIte.hasNext()){
				String ans = "NA";
				String query = queryIte.next();
				ArrayList<HashMap<String, String>> fin = inf.FOL_BC_ASK(query);
				ListIterator<HashMap<String, String>> itr = fin.listIterator();
				while(itr.hasNext()){
					if(itr.next().get("failure").equals("false")){
						ans = "TRUE";
					}
				}
				if(ans.equals("NA")){
					ans="FALSE";
				}
				writer.println(ans);
			}	
			sc.close();
			writer.close();
		}catch (IOException e){
			System.out.println("File not found");
		}	
	}
}
