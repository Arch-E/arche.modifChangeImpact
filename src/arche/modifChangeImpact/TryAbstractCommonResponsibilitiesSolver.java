/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact;

/**
 * This class implements the solver for the "abstract common responsibilities" tactic.
 * It searches for pairs of responsibilities that, if abstracted, can really improve 
 * the total cost of the scenario.
 * 
 * @author Andres Diaz-Pace
 */

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
//import java.util.logging.Level;

//import arche.example.hibernate.vo.ArchEResponsibilityDependencyRelationVO;
import arche.modifChangeImpact.hibernate.ArchECoreResponsibilityStructure;
import arche.modifChangeImpact.hibernate.vo.ArchEModuleVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;
import arche.modifChangeImpact.hibernate.vo.ArchEScenarioVO;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;
import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEResponsibilityStructure;
import edu.cmu.sei.arche.external.data.ArchEScenario;

public class TryAbstractCommonResponsibilitiesSolver implements ModifiabilityTacticSolver {

	private static final double THRESHOLD_COST = 0.003; 
	
	private ModuleADLWrapper myModuleView;
	private ArchECoreResponsibilityStructure myResponsibilityStructure;		
	private List<ArchEResponsibility> primaryResponsibilities;
	private ArchEResponsibilityVO targetResponsibilityA;
	private ArchEResponsibilityVO targetResponsibilityB;
	private ChangeImpactAnalyzer initialAnalyzer;
	private AbstractCommonResponsibilitiesChangeImpactAnalyzer bestAnalyzer;
	private AbstractCommonResponsibilitiesChangeImpactAnalyzer betterAnalyzer;
	private ArchEScenarioVO targetScenario = null;
	private Double bestAbstractionCost;
	
	public TryAbstractCommonResponsibilitiesSolver(ChangeImpactAnalyzer analyzer, List<ArchEResponsibility> scenarioResponsibilities) {
		myModuleView = null;
		myResponsibilityStructure = null;
		primaryResponsibilities = scenarioResponsibilities;
		targetResponsibilityA = null;
		targetResponsibilityB = null;
		initialAnalyzer = analyzer;
		bestAnalyzer = null;
		betterAnalyzer = null;
		targetScenario = null;
	}
	
	public void setResponsibilityStructure(ArchECoreResponsibilityStructure responsibilities) {
		myResponsibilityStructure = responsibilities;			
	}
	
	public void setModuleView(RFModuleView view) {
		myModuleView = (ModuleADLWrapper)view;			
	}
	
	private Double findBestAbstractionCost(ArchEResponsibilityVO respA, ArchEResponsibilityVO respB, double maxCost) {
		
		double reductionFactor = 0.9;
		
		AbstractCommonResponsibilitiesChangeImpactAnalyzer newAnalyzer = new AbstractCommonResponsibilitiesChangeImpactAnalyzer(myModuleView, myResponsibilityStructure);
		
		newAnalyzer.setTargetResponsibilities(respA, respB);
		try {
			newAnalyzer.doInterpretation(primaryResponsibilities);
			newAnalyzer.doEvaluation();
		} catch (ChangeImpactAnalysisException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}				
		double totalCost = newAnalyzer.getTotalCost();
		//System.out.println("Total cost: "+totalCost);
		
		if ((betterAnalyzer == null) || (totalCost < betterAnalyzer.getTotalCost()))
			betterAnalyzer = newAnalyzer;
		
		if (totalCost < reductionFactor * maxCost) {
			bestAnalyzer = newAnalyzer;
			return (totalCost);
		}
		else 
			return (null);
	}	
	
	public boolean searchForTactic(ArchEScenario scenario) {
		
		targetScenario = (ArchEScenarioVO)scenario;
		// The responsibilities are ordered according to coupling in descendent order
		Comparator<ArchEResponsibility> c = new ResponsibilityCostComparator(initialAnalyzer);
//		List<ArchEResponsibility> listResponsibilities = myResponsibilityStructure.getResponsibilities();
//		List<ArchEResponsibility> listResponsibilities = initialAnalyzer.getResponsibilities();
		List<ArchEResponsibility> listResponsibilities = myResponsibilityStructure.getResponsibilitiesByScenario(scenario);
		Collections.sort(listResponsibilities, c);
		
//		Iterator<ArchEResponsibility> itResponsibilities = listResponsibilities.iterator();
		
		bestAnalyzer = null;
		betterAnalyzer = null;
		targetResponsibilityA = null;
		targetResponsibilityB = null;
		double estimatedCostA = 0.0;
		double estimatedCostB = 0.0;
		boolean found = false;
		boolean stop = false;
		boolean denormalizedCost = false;
		
		for (int i = 0; (i < listResponsibilities.size()) && !stop ; i++) {
			targetResponsibilityA = (ArchEResponsibilityVO)(listResponsibilities.get(i));
			targetResponsibilityB = null;
			estimatedCostA = initialAnalyzer.getResponsibilityEstimatedCost(targetResponsibilityA,denormalizedCost);

			for (int j = i + 1; j < listResponsibilities.size(); j++) {
				targetResponsibilityB = (ArchEResponsibilityVO)(listResponsibilities.get(j));
				estimatedCostB = initialAnalyzer.getResponsibilityEstimatedCost(targetResponsibilityB,denormalizedCost);
				
				if (initialAnalyzer.isPrimaryResponsibility(targetResponsibilityA) 
						&& initialAnalyzer.isPrimaryResponsibility(targetResponsibilityB)
						&& (estimatedCostA > THRESHOLD_COST) && (estimatedCostB > THRESHOLD_COST)) {
					// Here, I have a candidate pair (A,B) that may or may not improve the scenario 
					// response when common parts are separated
//					System.out.println("======SEARCHING RESPONSIBILITIES TO ABSTRACT FOR: "+targetResponsibilityA.getName()+" - "+targetResponsibilityB.getName());			
					bestAbstractionCost = this.findBestAbstractionCost(targetResponsibilityA,targetResponsibilityB,initialAnalyzer.getTotalCost());
//					System.out.println("               Best cost found (so far) = "+bestAbstractionCost);

					// Check if I found something that improves the response?!
					if (betterAnalyzer != null)  // At least there's a minimum cost found 
						found = true;
				}			
			}			

			if (estimatedCostA <= THRESHOLD_COST)
				stop = true; // The remaining modules are also below the threshold
		}
		
		if (found) {
			List<ArchEResponsibilityVO> both = betterAnalyzer.getTargetResponsibilities();
			if (bestAnalyzer != null)
				both = bestAnalyzer.getTargetResponsibilities();
			targetResponsibilityA = both.get(0);
			targetResponsibilityB = both.get(1);
//			printLog(3, Level.INFO, "Setting responsibility target A --> " + targetResponsibilityA.getName());
//			printLog(3, Level.INFO, "Setting responsibility target B --> " + targetResponsibilityA.getName());
			return (true);
		}
		else {
			targetResponsibilityA = null;
			targetResponsibilityB = null;
//			printLog(3, Level.INFO, "Setting responsibility targets A & B --> NOT FOUND");
			return (false);
		}
	}
	
	public List getParameters() {	
		if ((targetResponsibilityA != null) && (targetResponsibilityB != null)) {
			
			List parameters = new ArrayList();

			parameters.add(targetResponsibilityA); // parameter <0> for the question
			parameters.add(targetResponsibilityB); // parameter <1> for the question
			
			Double currentCost = initialAnalyzer.getTotalCost();		
			Double improvedCostAfterSplitting = Double.MAX_VALUE;
			if (bestAnalyzer != null)
				improvedCostAfterSplitting = bestAnalyzer.getTotalCost();
			else if (betterAnalyzer != null)
				improvedCostAfterSplitting = betterAnalyzer.getTotalCost();
			
			parameters.add(currentCost); // parameter <2> for the question
			parameters.add(improvedCostAfterSplitting); // parameter <3> for the question
			parameters.add(targetScenario);
			
			return (parameters);
		}
		else
			return (null);
	}

	public List getTarget() {
		
		List targets = new ArrayList();			
		if ((targetResponsibilityA != null) && (targetResponsibilityB != null)) {
			targets.add(targetResponsibilityA);
			targets.add(targetResponsibilityB);
			return (targets);
		}
		else
			return (null);
	}

	public List estimateContext() {
		List at = new ArrayList();
		if ((targetResponsibilityA != null) && (targetResponsibilityB != null)) {
			at.add(targetResponsibilityA);
			at.add(targetResponsibilityB);
		}
	
		return (at);
	}

	// This internal class will order responsibilities in a descending order
	// according to their individual costs
	class ResponsibilityCostComparator implements Comparator<ArchEResponsibility> {
	
		private ChangeImpactAnalyzer analyzer = null;
	
		public ResponsibilityCostComparator(ChangeImpactAnalyzer anAnalyzer) {
			analyzer = anAnalyzer;
		}

		public int compare(ArchEResponsibility resp1, ArchEResponsibility resp2) {
			double cost1 = analyzer.getResponsibilityEstimatedCost(resp1);
			double cost2 = analyzer.getResponsibilityEstimatedCost(resp2);
			if (cost1 < cost2)
				return (1);
			else if (cost1 > cost2)
				return (-1);
			else
				return (0);
		}

	}

	// This internal class simulates that the common part of responsibilities A & B
	// has been segregated, and then estimates the resulting cost of that tactic.
	class AbstractCommonResponsibilitiesChangeImpactAnalyzer extends ChangeImpactAnalyzer {
		
	private ArchEResponsibilityVO targetResponsibilityA = null; // To responsibilities to be split
	private ArchEResponsibilityVO targetResponsibilityB = null; // To responsibilities to be split
	private int positionTargetA = -1;
	private int positionTargetB = -1;
	private List<ArchEResponsibility> mainPrimaryResponsibilities = null;
	private List<ArchEResponsibility> newPrimaryResponsibilities = null;
	private List<ArchEModuleVO> newPrimaryModules = null; 
	private ArchEResponsibilityVO childRespA;
	private ArchEResponsibilityVO childRespB;
	private ArchEResponsibilityVO sharedRespAB;
	private ArchEModuleVO modRespA;
	private ArchEModuleVO modRespB;
	private ArchEModuleVO modSharedRespAB;

	public AbstractCommonResponsibilitiesChangeImpactAnalyzer(RFModuleView adl, ArchEResponsibilityStructure respStructure)  {
		super (adl, respStructure);

		ArchEVersionVO versionVO = (ArchEVersionVO)moduleView.getParent().getCurrentVersion();
		childRespA = new ArchEResponsibilityVO(versionVO); 
		childRespA.setName("internalChildRespA");
		childRespB = new ArchEResponsibilityVO(versionVO); 
		childRespB.setName("internalChildRespB");
		sharedRespAB = new ArchEResponsibilityVO(versionVO); 
		sharedRespAB.setName("internalSharedRespAB");
		modRespA = new ArchEModuleVO(versionVO);
		modRespA.setName("internalChildModuleA");					
		modRespB = new ArchEModuleVO(versionVO);
		modRespB.setName("internalChildModuleB");					
		modSharedRespAB = new ArchEModuleVO(versionVO);
		modSharedRespAB.setName("internalSharedModuleAB");					

	}
	
	public void setTargetResponsibilities(ArchEResponsibilityVO respA, ArchEResponsibilityVO respB) {
		targetResponsibilityA = respA;		
		targetResponsibilityB = respB;		
		return;		
	}
	
	public List<ArchEResponsibilityVO> getTargetResponsibilities() {
		List<ArchEResponsibilityVO> both = new ArrayList<ArchEResponsibilityVO>();
		both.add(targetResponsibilityA);
		both.add(targetResponsibilityB);
		return (both);
	}

	public boolean doInterpretation(List<ArchEResponsibility> scenarioResponsibilities) 
			throws ChangeImpactAnalysisException {

		mainPrimaryResponsibilities = scenarioResponsibilities;
		// This is a re-interpretation of the primary responsibilities and modules
		newPrimaryResponsibilities = new ArrayList<ArchEResponsibility>();
		for (Iterator<ArchEResponsibility> itt = mainPrimaryResponsibilities.iterator(); itt.hasNext(); )
			newPrimaryResponsibilities.add(itt.next());

		// The responsibility for the children
		double costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEFAULT_RESPONSIBILITY_COST);
		super.addPrimaryResponsibility(sharedRespAB, costR); // The common responsibility (added at position 0)

		costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEFAULT_RESPONSIBILITY_COST);
		ArchEResponsibility respItem = null;
		for (Iterator<ArchEResponsibility> itResps = newPrimaryResponsibilities.iterator(); itResps.hasNext();) {
			respItem = itResps.next();
			try {
				costR = respItem.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE);
				costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(costR);
			} catch (ArchEException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}		
			super.addPrimaryResponsibility(respItem, costR);
		}

		double costM = ChangeImpactAnalyzer.normalizeModuleCost(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		super.addPrimaryModule(modSharedRespAB, costM); // The module for the shared responsibility (added at position 0) 

		newPrimaryModules = computeNewRelatedPrimaryModules(newPrimaryResponsibilities);
		ArchEModuleVO modItem = null;
		for (Iterator<ArchEModuleVO> itMods = newPrimaryModules.iterator(); itMods.hasNext();) {
			modItem = itMods.next();
			costM = ChangeImpactAnalyzer.normalizeModuleCost(modItem.getCostOfChange());

			if (this.getPrimaryModuleIndex(modItem) == -1) {
//				if (!moduleView.isAllocated(targetResponsibility,modItem)) 
//					super.addPrimaryModule(modItem, costM);				
//				else if (moduleView.getResponsibilitiesByModule(modItem).size() > 1) 
					super.addPrimaryModule(modItem, costM);		
			}
		}

		List<ArchEResponsibility> temp = computeNewDependentResponsibilities(mainPrimaryResponsibilities);
		newPrimaryResponsibilities.addAll(temp);
		costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEPENDENT_RESPONSIBILITY_COST);
		respItem = null;
		for (Iterator<ArchEResponsibility> itResps = temp.iterator(); itResps.hasNext();) {
			respItem = itResps.next();	
			if (this.getPrimaryResponsibilityIndex(respItem) == -1)
				super.addPrimaryResponsibility(respItem, costR);
		}
			
		newPrimaryModules = computeNewRelatedPrimaryModules(newPrimaryResponsibilities);
		
		temp = computeNewInferredResponsibilities(newPrimaryResponsibilities, newPrimaryModules);
		newPrimaryResponsibilities.addAll(temp);
		costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEPENDENT_RESPONSIBILITY_COST);
		respItem = null;
		for (Iterator<ArchEResponsibility> itResps = temp.iterator(); itResps.hasNext();) {
			respItem = itResps.next();			
			if (this.getPrimaryResponsibilityIndex(respItem) == -1)
				super.addPrimaryResponsibility(respItem, costR);
		}

		costM = ChangeImpactAnalyzer.normalizeModuleCost(ChangeImpactAnalyzer.DEPENDENT_MODULE_COST);
		modItem = null;
		for (Iterator<ArchEModuleVO> itMods = newPrimaryModules.iterator(); itMods.hasNext();) {
			modItem = itMods.next();
			costM = ChangeImpactAnalyzer.normalizeModuleCost(modItem.getCostOfChange());

			if (this.getPrimaryModuleIndex(modItem) == -1) {
//				if (!moduleView.isAllocated(targetResponsibility,modItem)) 
//					super.addPrimaryModule(modItem, costM);				
//				else if (moduleView.getResponsibilitiesByModule(modItem).size() > 1) 
					super.addPrimaryModule(modItem, costM);		
			}
		}
		
		// The positions for responsibilities A & B is stored for further use
		positionTargetA = -1;
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) {
			if (primaryResponsibilities[i].equals(targetResponsibilityA)) 
				positionTargetA = i;
		}		
		positionTargetB = -1;
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) {
			if (primaryResponsibilities[i].equals(targetResponsibilityB)) 
				positionTargetB = i;
		}		

		return (true);
	}

	private List<ArchEResponsibility> computeNewDependentResponsibilities(List<ArchEResponsibility> responsibilities) {
		// It adds a number of "dependent" responsibilities to the scope of primary responsibilities
		List<ArchEResponsibility> dependents = new ArrayList<ArchEResponsibility>();
		ArchEResponsibility resp = null;
		ArchEResponsibility temp = null;
		for (Iterator<ArchEResponsibility> it = responsibilities.iterator(); it.hasNext();) {
			resp = it.next();
			for(Iterator<ArchEResponsibility> itSec = this.deriveSecondaryResponsibilitiesFor(resp).iterator(); itSec.hasNext();) {
				temp = itSec.next();
				if (!responsibilities.contains(temp) && !dependents.contains(temp)) 
					dependents.add(temp);
			}
		}
		return (dependents);
	}
	
	private List<ArchEModuleVO> computeNewRelatedPrimaryModules(List<ArchEResponsibility> responsibilities) { 
		
		List<ArchEModuleVO> primaryModules = new ArrayList<ArchEModuleVO>();
		ArchEResponsibility resp = null;
		ArchEModuleVO mod = null;
		List<ArchEModuleVO> primaryModulesResp = null;
		boolean becomesOrphanModule = false;
		for (Iterator<ArchEResponsibility> itResps = responsibilities.iterator(); itResps.hasNext(); ) {
			resp = itResps.next();
			primaryModulesResp = moduleView.getModulesByResponsibility(resp);
			for (Iterator<ArchEModuleVO> itMods = primaryModulesResp.iterator(); itMods.hasNext();) {
				mod = itMods.next();
				becomesOrphanModule = false; // Because it only contains the responsibility to be split
//				if (resp.equals(targetResponsibility) && (moduleView.getResponsibilitiesByModule(mod).size() == 1))
//					becomesOrphanModule = true;						
				if (!primaryModules.contains(mod) && !becomesOrphanModule)
					primaryModules.add(mod);
			}
		}

		return (primaryModules);
	}
	
	private List<ArchEResponsibility> computeNewInferredResponsibilities(List<ArchEResponsibility> responsibilities, List<ArchEModuleVO> modules) {
		List<ArchEResponsibility> inferredResponsibilities = new ArrayList<ArchEResponsibility>();
		ArchEResponsibility inferredPrimary = null;
		for (Iterator<ArchEResponsibility> itResps = allResponsibilities.getResponsibilities().iterator(); itResps.hasNext();) {
			inferredPrimary = itResps.next();
			if (!responsibilities.contains(inferredPrimary)) {
				for (Iterator<ArchEModuleVO> itMods = modules.iterator(); itMods.hasNext();) {
					if (moduleView.isAllocated(inferredPrimary, itMods.next()) 
							&& (!inferredResponsibilities.contains(inferredPrimary)))
						inferredResponsibilities.add(inferredPrimary);
				}					
			}
		}
		return (inferredResponsibilities);
	}
	
//	private boolean isOrphanModule(ArchEModuleVO module) {
//		if (moduleView.isAllocated(targetResponsibility, module)) { 
//			List<ArchEResponsibility> resps = moduleView.getResponsibilitiesByModule(module);
//			if (resps.size() <= 1)
//				return (true);
//			else {
//				ArchEResponsibilityVO respMine = null;
//				ArchEResponsibilityVO respOthers = null;
//				String relationType = ArchEResponsibilityDependencyRelationVO.class.getName();
//				for (Iterator<ArchEResponsibility> itMine = resps.iterator(); itMine.hasNext();) {
//					respMine = (ArchEResponsibilityVO)(itMine.next());
//					for (Iterator<ArchEResponsibility> itOthers = mainPrimaryResponsibilities.iterator(); itOthers.hasNext();) {
//						respOthers = (ArchEResponsibilityVO)(itOthers.next());
//						if (!respMine.equals(respOthers) && !respMine.equals(targetResponsibility) 
//								&& allResponsibilities.existRelation(respMine, respOthers, relationType)) {
//							//System.out.println("Relationship: "+respOthers.getName()+" -- "+respMine.getName());
//							return (false);
//						}
//					}					
//				}
//				return (true);
//			}
//		}		
//		//System.out.println("Not targetResponsibility allocated!!");
//		return (false);		
//	}

	private void updateChangeProbabilityResponsibilitiesDueToAbstraction() {
		if (positionTargetA > -1) { //  Update the parts of the matrix due to the splitting of  responsibility A
			for (int j = 1; j <= indexPrimaryResponsibilities; j++) { // The new shared responsibility is at position 0
				respDependencies[positionTargetA][j] = 0.45 * respDependencies[positionTargetA][j];
				respDependencies[j][positionTargetA] = 0.45 * respDependencies[j][positionTargetA];
			}
			// The value of 0.45 is necessary to be similar to that of the tactic
			respDependencies[0][positionTargetA] = 0.45 * DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
			respDependencies[positionTargetA][0] = 0.45 * DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
		}

		if (positionTargetB > -1) { //  Update the parts of the matrix due to the splitting of  responsibility B
			for (int j = 1; j <= indexPrimaryResponsibilities; j++) { // The new shared responsibility is at position 0
				respDependencies[positionTargetB][j] = 0.45 * respDependencies[positionTargetB][j];
				respDependencies[j][positionTargetB] = 0.45 * respDependencies[j][positionTargetB];
			}
			// The value of 0.45 is necessary to be similar to that of the tactic
			respDependencies[0][positionTargetB] = 0.45 * DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
			respDependencies[positionTargetB][0] = 0.45 * DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
		}

		return;		
	}

	private void updateChangeProbabilityModulesDueToAbstraction() {

		int positionModule = -1;
		if (positionTargetA > -1) {//  Update the parts of the matrix due to the splitting of the tactic					
			for (int i = 1; i <= indexPrimaryModules; i++) {				
				if (moduleView.isAllocated(targetResponsibilityA, primaryModules[i]) 
						&& !moduleView.isAllocated(targetResponsibilityB, primaryModules[i])) {
					positionModule = i;
					modDependencies[0][positionModule] = respDependencies[0][positionTargetA];
					modDependencies[positionModule][0] = respDependencies[positionTargetA][0];
				}
			}
		}
		if (positionTargetB > -1) {//  Update the parts of the matrix due to the splitting of the tactic					
			for (int i = 1; i <= indexPrimaryModules; i++) {				
				if (moduleView.isAllocated(targetResponsibilityB, primaryModules[i]) 
					&& !moduleView.isAllocated(targetResponsibilityA, primaryModules[i])) {
					positionModule = i;
					modDependencies[0][positionModule] = respDependencies[0][positionTargetB];
					modDependencies[positionModule][0] = respDependencies[positionTargetB][0];
				}
			}
		}

		if ((positionTargetB > -1) && (positionTargetB > -1)) {//  Update the parts of the matrix due to the splitting of the tactic					
			for (int i = 1; i <= indexPrimaryModules; i++) {				
				if (moduleView.isAllocated(targetResponsibilityB, primaryModules[i]) 
					&& moduleView.isAllocated(targetResponsibilityA, primaryModules[i])) {
					positionModule = i;
					modDependencies[0][positionModule] = ( respDependencies[0][positionTargetB] + respDependencies[0][positionTargetA] ) / 2.0;
					modDependencies[positionModule][0] = ( respDependencies[positionTargetB][0] + respDependencies[positionTargetB][0] ) / 2.0;
				}
			}
		}

		return;
	}

	// This overrides the functionality of the original method in ChangeImpactAnalyzer,
	// in order to factor in the abstraction of the shared responsibility
	protected void estimateCostOfChangePrimaryModules() {
		
		double costNeighbors = 0.0;
		double costAllocatedResponsibilities = 0.0;
		double count = 0;		
		ArchEResponsibility resp = null;
		
		for (int i = 1; i <= indexPrimaryModules; i++) {// The new shared child is at positions 0 
			
			// This part is for the cost of adjacent modules
			count = 0;
			costNeighbors = 0.0;
			for (int j = 0; j <= indexPrimaryModules; j++) {
				if ((modDependencies[j][i] > 0) && (i != j)) {
					costNeighbors = costNeighbors + modDependencies[j][i] * modBasicCosts[j];
					count++;					
				}
			}
			if (count > 0)
				costNeighbors = costNeighbors / count;
			
			// This part is for the cost of allocated responsibilities
			costAllocatedResponsibilities = 0.0;
			count = 0;
			for (int k = 0; k <= indexPrimaryResponsibilities; k++) {
				resp = primaryResponsibilities[k];
				if (moduleView.isAllocated(resp, primaryModules[i])) {
					if ((k == positionTargetA) || (k == positionTargetB))
						costAllocatedResponsibilities = costAllocatedResponsibilities + 0.3 * respBasicCosts[k];
					else 
						costAllocatedResponsibilities = costAllocatedResponsibilities + respBasicCosts[k];
					count++;
				}
			}
			if (count > 0)
				costAllocatedResponsibilities = costAllocatedResponsibilities / count;
			
			double ratio = count / (allResponsibilities.getResponsibilities().size() + 1);
			modComputedCosts[i] = ratio*modBasicCosts[i] + 0.35*costNeighbors + 0.35*costAllocatedResponsibilities;	
			if (modComputedCosts[i] > 1)
				modComputedCosts[i] = 1.0;		
		}
		
		// Note: This is the cost for the shared children responsibility
		count = 1;
		costNeighbors = 0.0;
		for (int j = 1; j <= indexPrimaryModules; j++) {
			if (modDependencies[j][0] > 0) {
				costNeighbors = costNeighbors + modDependencies[j][0] * modBasicCosts[j];
				count++;					
			}
		}
		if (count > 0)
			costNeighbors = costNeighbors / count;

		double costShared = ChangeImpactAnalyzer.DEFAULT_RESPONSIBILITY_COST;
		try {
			costShared = 0.7* (targetResponsibilityA.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE) 
					+ targetResponsibilityB.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE)) / 2.0;
			if (costShared < ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST)
				costShared = ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST;
		} catch (ArchEException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		costAllocatedResponsibilities = ChangeImpactAnalyzer.normalizeResponsibilityCost(costShared);
		double ratio1 = 1.0 / (allResponsibilities.getResponsibilities().size() + 1);
		modComputedCosts[0] = ratio1*ChangeImpactAnalyzer.normalizeModuleCost(ChangeImpactAnalyzer.DEFAULT_MODULE_COST) 
				+ 0.35*costNeighbors + 0.35*costAllocatedResponsibilities;
		if (modComputedCosts[0] > 1)
			modComputedCosts[0] = 1.0;

		return;		
	}

	
	public void doEvaluation() {
		
		this.resetOutputParameters();		

		// These are preparatory computations to calculate the figures
		this.computeChangeProbabilityResponsibilities();
		//this.printResponsibilityDependencies();
		this.computeChangeProbabilityModules();
		//this.printModuleDependencies();
		this.updateChangeProbabilityResponsibilitiesDueToAbstraction();
		//this.printResponsibilityDependencies();
		this.updateChangeProbabilityModulesDueToAbstraction();
		//this.printModuleDependencies();

		// These are all the figures estimated by the analyzer (for a given class of change)
		this.estimateCostOfChangePrimaryModules();
		
		//this.printModuleEstimatedCosts();
		
		needsComputation = false;
	}

	}

}
